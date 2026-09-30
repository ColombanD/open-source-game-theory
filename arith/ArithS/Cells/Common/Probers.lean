import ArithS.Cells.Common.Bots
import ArithS.Eval.EvalN

/-!
# ArithS.Cells.Common.Probers — search clauses and prober steps in every model

Consolidation stage 4 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24). The `EvalGraph` lemmas that
every cell file re-proved for its own searcher or prober, MOVED here unchanged (names, statements,
proofs) from `Cells/DupocMirror`, `Cells/DIMCID`, `Cells/PrudentMirror`, `Cells/KhatCells`,
`Cells/FlipCells`, `Cells/JustBot` and `Cells/PositiveCells`, plus the two NEW roots
`search_then_V₆`/`search_else_V₆` (the two directions of `EvalGraph.search_iff₆`, packaged):

1. **Search clauses in any frame**: the generic searcher's then-clause `SV_then_V`/`botSV_then_V`, its
   self-frame form `SV_search_V`, the hand-written Dupoc/Cupod clauses `dupoc/cupod_frame_search_V`,
   `botDupoc/botCupod_frame_search_V`, `dupoc/cupod_search_any_V`.
2. **Mirror**: the sim step `mirror_step_V`, the copies `mirror_copies2_V` (2 → 3) and `mirror_copies3_V`
   (3 → 4), the prudence facts `mirror_bot_defect_V`/`mirror_bot_coop_V`.
3. **TitForTat**: `tft_C_of_probe_C_V`, `tftT_D_of_probe_D_V`.
4. **Constants**: `const_play_V`, `bot_const_play_V`, `const_not_play_V`, `bot_const_not_play_V`.

Per-bot instances (`mirror_copies_dupoc_V`, `dimcid_search_V`, `prudent_search_V`, …) stay with their
bots. The ℕ-only probers (`dbot_*`, `obot_*`, `ebot_*`, `mirror_copies`) stay in `Cells/SoundnessCells`
(`ebot_D_of_probes_D` moved there from `Cells/DimcidFlips`; `just7_else_V`/`just7_D_of_probe` moved to
`Cells/JustSlot`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The two directions of the search clause on a six-variable template -/

section search

/-- **The then-clause of a search node on a six-variable template, in any frame**: the guard found within
`k` and the then-branch playing `a` at fuel `n` make the searcher play `a` at fuel `n + 1`
(`EvalGraph.search_iff₆`, the left disjunct). -/
theorem search_then_V₆ {n me opp k g p q a : V} (hg : IsSemiformula LAct 6 g)
    (h : LenBox TAct k (guardCode g me opp)) (hp : EvalGraph n me opp p a) :
    EvalGraph (n + 1) me opp (pSearch k g p q) a :=
  (EvalGraph.search_iff₆ hg).mpr (Or.inl ⟨h, hp⟩)

/-- **The else-clause**: the guard NOT found within `k` and the else-branch playing `a` at fuel `n` make the
searcher play `a` at fuel `n + 1` (the right disjunct). -/
theorem search_else_V₆ {n me opp k g p q a : V} (hg : IsSemiformula LAct 6 g)
    (h : ¬ LenBox TAct k (guardCode g me opp)) (hq : EvalGraph n me opp q a) :
    EvalGraph (n + 1) me opp (pSearch k g p q) a :=
  (EvalGraph.search_iff₆ hg).mpr (Or.inr ⟨h, hq⟩)

end search

/-! ### 2. The searchers' clauses in any frame -/

section searchers

/-- **The generic searcher's then-clause in ANY frame** (fuel 2): a proof of `guardCode ⌜g⌝ me opp`
within `k` makes `SV g a k` play `a`. -/
theorem SV_then_V (g : Semisentence LAct 6) (a : ℕ) (k me opp : V)
    (h : LenBox TAct k (guardCode (⌜g⌝ : V) me opp)) : EvalGraph 2 me opp (SV g a k) (a : V) := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) (a : V)
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- The bot-wrapped generic searcher's then-clause in any frame (fuel 3). -/
theorem botSV_then_V (g : Semisentence LAct 6) (a : ℕ) (k me opp : V)
    (h : LenBox TAct k (guardCode (⌜g⌝ : V) me opp)) : EvalGraph 3 me opp (pBot (SV g a k)) (a : V) := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact SV_then_V g a k me opp h

/-- **The search clause of the generic engine searcher in every model** (fuel 2): found ⇒ the then-branch. -/
theorem SV_search_V (g : Semisentence LAct 6) (a : ℕ) (k opp : V)
    (h : LenBox TAct k (guardCode (⌜g⌝ : V) (SV g a k) opp)) :
    EvalGraph 2 (SV g a k) opp (SV g a k) (a : V) := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (SV g a k) opp (pSearch k (⌜g⌝ : V) (pConst (a : V)) (pConst ((1 - a : ℕ) : V))) (a : V)
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ g)]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (SV g a k) opp (pConst (a : V)) (a : V) := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **Dupoc's search clause in ANY frame** (fuel 2): `DupocV k` run in the frame `(me, opp)` plays
`C` if `guardCode ⌜guardTemplate 0⌝ me opp` is provable within `k`. -/
theorem dupoc_frame_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) me opp) → EvalGraph 2 me opp (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜guardTemplate 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 0))]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **Cupod's search clause in ANY frame** (fuel 2). -/
theorem cupod_frame_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) me opp) → EvalGraph 2 me opp (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) me opp (pSearch k (⌜guardTemplate 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 1))]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) me opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **The bot-wrapped Dupoc's search clause in any frame** (fuel 3: the bot step, the search step,
the constant). -/
theorem botDupoc_frame_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) me opp) → EvalGraph 3 me opp (pBot (DupocV k)) 0 := by
  intro h
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact dupoc_frame_search_V k me opp h

theorem botCupod_frame_search_V (k me opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) me opp) → EvalGraph 3 me opp (pBot (CupodV k)) 1 := by
  intro h
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm, EvalGraph.bot_iff]
  exact cupod_frame_search_V k me opp h

/-- **Cupod's search clause against ANY opponent in every model** (fuel `2`). -/
theorem cupod_search_any_V (k opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) opp) →
      EvalGraph 2 (CupodV k) opp (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CupodV k) opp (pSearch k (⌜guardTemplate 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 1))]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (CupodV k) opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **Dupoc's search clause against ANY opponent in every model** (fuel `2`). -/
theorem dupoc_search_any_V (k opp : V) :
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) opp) →
      EvalGraph 2 (DupocV k) opp (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DupocV k) opp (pSearch k (⌜guardTemplate 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (guardTemplate 0))]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

end searchers

/-! ### 3. Mirror's sim step and copies, the prudence facts -/

section mirror

/-- **Mirror's sim step in every model**: Mirror in the frame `(Mirror, opp)` runs `opp` in the
frame `(opp, Mirror)` (`EvalGraph.sim_iff` + `substCode_opp`/`substCode_self`). -/
theorem mirror_step_V (n opp a : V) :
    EvalGraph (n + 1) MirrorV opp MirrorV a ↔ EvalGraph n opp MirrorV opp a := by
  have h := EvalGraph.sim_iff (n := n) (me := MirrorV) (opp := opp) (p := pOpp) (q := pSelf) (a := a)
  rw [substCode_opp, substCode_self] at h
  exact h

/-- Mirror copies, in every model: a fuel-2 play of `opp` against Mirror is Mirror's fuel-3 play
against `opp` (`mirror_step_V`). -/
theorem mirror_copies2_V (opp a : V) (h : EvalGraph 2 opp MirrorV opp a) :
    EvalGraph 3 MirrorV opp MirrorV a := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  exact (mirror_step_V 2 opp a).mpr h

/-- Mirror copies a fuel-3 play at fuel 4. -/
theorem mirror_copies3_V (opp a : V) (h : EvalGraph 3 opp MirrorV opp a) :
    EvalGraph 4 MirrorV opp MirrorV a := by
  rw [show (4 : V) = 3 + 1 by norm_num]
  exact (mirror_step_V 3 opp a).mpr h

/-- **Prudence is a true closed Σ₁ fact in every model**: Mirror plays D against `.bot DefectBot`
(fuel 3: the sim step, the bot step, the constant). -/
theorem mirror_bot_defect_V : EvalGraph 3 MirrorV (pBot (pConst 1)) MirrorV (1 : V) := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 1)) MirrorV (pConst 1) (1 : V) := EvalGraph.const_iff.mpr rfl
  rw [zero_add] at e0
  have e1 : EvalGraph (1 + 1) (pBot (pConst 1)) MirrorV (pBot (pConst 1)) (1 : V) := EvalGraph.bot_iff.mpr e0
  rw [one_add_one_eq_two] at e1
  have e2 := (mirror_step_V 2 (pBot (pConst 1)) 1).mpr e1
  rwa [two_add_one_eq_three] at e2

/-- The transposed prudence fact: Mirror plays C against `.bot CooperateBot`. -/
theorem mirror_bot_coop_V : EvalGraph 3 MirrorV (pBot (pConst 0)) MirrorV (0 : V) := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 0)) MirrorV (pConst 0) (0 : V) := EvalGraph.const_iff.mpr rfl
  rw [zero_add] at e0
  have e1 : EvalGraph (1 + 1) (pBot (pConst 0)) MirrorV (pBot (pConst 0)) (0 : V) := EvalGraph.bot_iff.mpr e0
  rw [one_add_one_eq_two] at e1
  have e2 := (mirror_step_V 2 (pBot (pConst 0)) 0).mpr e1
  rwa [two_add_one_eq_three] at e2

end mirror

/-! ### 4. TitForTat's probe steps -/

section tft

/-- **TFT cooperates with `x` when `x` cooperates with `.bot CooperateBot`, in every model** (fuel `+2`). -/
theorem tft_C_of_probe_C_V {x n : V} (h : EvalGraph n x (pBot (pConst 0)) x 0) :
    EvalGraph (n + 1 + 1) TftV x TftV 0 := by
  unfold TftV
  rw [EvalGraph.ite_iff]
  refine ⟨0, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

/-- **The transposed TFT defects against `x` when `x` defects against `.bot DefectBot`** (fuel `+2`). -/
theorem tftT_D_of_probe_D_V {x n : V} (h : EvalGraph n x (pBot (pConst 1)) x 1) :
    EvalGraph (n + 1 + 1) TftTV x TftTV 1 := by
  unfold TftTV
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inl ⟨rfl, EvalGraph.const_iff.mpr rfl⟩⟩
  rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
  exact h

end tft

/-! ### 5. The constants -/

section constants

/-- A constant plays itself against anything, in every model (fuel 1). -/
lemma const_play_V (me opp a : V) : ∃ n : V, EvalGraph n me opp (pConst a) a :=
  ⟨0 + 1, EvalGraph.const_iff.mpr rfl⟩

/-- A frozen constant plays itself against anything, in every model (fuel 2). -/
lemma bot_const_play_V (me opp a : V) : ∃ n : V, EvalGraph n me opp (pBot (pConst a)) a :=
  ⟨0 + 1 + 1, EvalGraph.bot_iff.mpr (EvalGraph.const_iff.mpr rfl)⟩

/-- A constant never plays the other value, in every model (determinism). -/
lemma const_not_play_V (me opp : V) {a b : V} (hab : a ≠ b) : ¬ ∃ n : V, EvalGraph n me opp (pConst a) b := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := const_play_V me opp a
  exact hab (EvalGraph.unique_V' m n _ _ _ _ _ hm hn)

lemma bot_const_not_play_V (me opp : V) {a b : V} (hab : a ≠ b) : ¬ ∃ n : V, EvalGraph n me opp (pBot (pConst a)) b := by
  rintro ⟨n, hn⟩
  obtain ⟨m, hm⟩ := bot_const_play_V me opp a
  exact hab (EvalGraph.unique_V' m n _ _ _ _ _ hm hn)

end constants

end ArithS

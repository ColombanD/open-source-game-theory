import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Cells.PrudentLoose — the two Prudent loose ends: the prudence `k̂`-chain and Prudent × `.bot MirrorBot`

`Research/Notes/ROUTE_B_SCOPE.md` §6 ("Prudent loose ends") and `ARITHMETIZED_S_RESULTS.md` "The floors
as dichotomies". `Cells/FloorDichotomy` left Prudent's PRUDENCE guard `B_k` — "the opponent defects against
`.bot DefectBot`" (`phiPi`) — as a hinge of its own in five nested dichotomies, and stated Prudent × EBot's `¬A` world
on Prudent's side only. This module settles what can be settled.

**(a) The prudence `k̂`-chain.** For an opponent that is an engine searcher `SV g a k` (a constant template, the budget
in the search slot), the prudence guard is the `binNumeral k`-instance of ONE fixed formula `qPiS g a` (Prudent described
above `KP` by `(TP, uP, wP)`, the opponent by its canonical `SV` triple; the me-slots are inert). When the opponent's
play against `.bot DefectBot` is its THEN-branch — its guard against the closed probe is a positive fact, found in every
model above a threshold (`found_of_all_V`) — `qPiS g a (k)` is TRUE in every model of `TAct` above a threshold, in both
readings, so `TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 qPiS g a)` by completeness (`tact_all_above_of_both`) and the instance fits `k` for
all large `k` (`found_of_all_above`): the prudence hinge is FOUND. This is the case for exactly the three opponents the
verdict pass rated (P): **Guardian** (its guard "`.bot DefectBot` defects against `.bot CooperateBot`" is a true closed
atom, `guardian_botDB_V`), **Wary** (its `.neg` guard "`.bot DefectBot` does not cooperate with me" is a Π₁ truth by
determinism, `wary_botDB_V`) and **Cupod** (its guard "`.bot DefectBot` defects against me", `cupod_botDB_V`); the τ-twins
(`guardianT_botCB_V`, `waryT_botCB_V`, `dupoc_botCB_V`) supply the swapped reading. Theorems
`prudence_found_vs_GuardianBot/_WaryBot/_CupodBot` and the RESTATED dichotomies
`dich_GuardianBot_vs_PrudentBot_prudenceFound`, `dich_WaryBot_vs_PrudentBot_prudenceFound`,
`dich_CupodBot_vs_PrudentBot_prudenceFound`, `dich_PrudentBot_vs_CupodBot_prudenceFound` — the prudence hinge discharged,
only the remaining hinge(s) inline (the originals in `Cells/FloorDichotomy` untouched).

**NOT discharged, and why (recorded, not a gap in a proof):** the two other "prudence" cells, **Just × Prudent** and
**CIMCIC × Prudent**. There the opponent's defection against `.bot DefectBot` is its ELSE-branch (Just's guard
"`.bot DefectBot` cooperates with `.bot (DupocBot k)`" is FALSE; CIMCIC's guard against `.bot DefectBot` is self-refuting)
— `B_k` is then equivalent to "`TAct` does NOT prove the opponent's guard within `k`", a bounded-consistency-type
sentence that is TRUE in ℕ but NOT true in every model of `TAct` (a nonstandard proof of the false guard makes the
searcher take its then-branch), so completeness cannot make it a `TAct`-theorem, and its provability within `k` is
exactly the (G) residue of `Cells/FloorVerdicts` (`floor_JustBot_vs_PrudentBot_true`, `floor_CIMCIC_vs_PrudentBot_true`
are the truth halves). For Just there is the further §7 obstruction: `progCode (JustBot k)` stores a `k`-dependent
template, so no fixed formula has the prudence guard as its `binNumeral k`-instance at all. Both cells keep `B` as a hinge.

**(b) Prudent × `.bot MirrorBot` by Löb.** EBot's third rung asks "Prudent cooperates with `.bot MirrorBot`"; in the
engine this is `prudent_botmirror_coop` (`Theorems/PrudentBot/vs_EBot.lean`). Here it is `Cells/PrudentMirror`'s family
re-instantiated at the CLOSED opponent `pBot Mirror` (`describes_closed`): the fixed formulas `qPB1` ("`.bot MirrorBot`
plays C against `Prudent k`") and `qPB2` ("`.bot MirrorBot` plays D against `.bot DefectBot`", the prudence conjunct),
their τ-twins, the family `pPB = (qPB1 ⋏ qPB2) ⋏ (τqPB1 ⋏ τqPB2)` with `loebSound_pPB : LoebSound pPB (14 + KP) 16`
(the two-level ∧-elimination hands each searcher both its guards; `.bot MirrorBot` copies at fuel 5 — the `.bot`
unwrapping is one fuel more than Mirror's fuel 4, `botMirror_step_V`; the prudence facts `botMirror_botDB_V`/
`botMirror_botCB_V` at fuel 4), and `family_found`. **`loeb_PrudentBot_vs_botMirror`**: for all large `k`,
`EvalGraph 3 (progCode (PrudentBot k)) (pBot Mirror) (progCode (PrudentBot k)) C ∧ EvalGraph 5 (pBot Mirror) (progCode (PrudentBot k)) (pBot Mirror) C`
(fuels: 3 = outer search, inner search, constant — as against Mirror; 5 = the `.bot` step, the sim step, Prudent's 3);
the box form `loeb_PrudentBot_vs_botMirror_guards`; the τ-twin `loeb_PrudentT_vs_botMirror`.

**Prudent × EBot closed in both worlds.** EBot's ladder against `PrudentBot k`: rung 1 (`.bot DefectBot`) Prudent
defects (`snd_PrudentBot_vs_botDB`), rung 2 (`.bot CooperateBot`) Prudent defects (`snd_PrudentBot_vs_botCB`), rung 3
(`.bot MirrorBot`) Prudent COOPERATES (b) — so EBot cooperates (`ebot_C_of_probes3`), whatever Prudent's outer verdict
against EBot itself: `floor_PrudentBot_vs_EBot_right` (EBot's C, the settled half) and
**`dich_PrudentBot_vs_EBot_full : ∃ k₀, ∀ k > k₀, (¬A_k → (D, C)) ∧ (A_k → (C, C))`** at the engine's fuel 7, with
`A_k` Prudent's outer hinge "EBot plays C against me" — the `¬A_k` world is now the engine's full `(D, C)`.

Naming per `Cells/Names.lean`: `prudence_found_vs_<X>` (the prudence guard found, engine head symbols), `dich_…_prudenceFound`
(the dichotomy with `B` discharged), `loeb_PrudentBot_vs_botMirror` (engine code, the frozen probe `botMirror`),
`loeb_Prudent_vs_botMirror_core` (the arith code), `floor_PrudentBot_vs_EBot_right`, `dich_PrudentBot_vs_EBot_full`.

Conventions: every threshold EXISTENTIAL; `simp` never sees a closed quote; `V` pinned in every statement; `≤` at ℕ
bridged by `le_def`; no `sorry`, no `axiom`, no `native_decide`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

-- `Type`, not `Type*`: the `Describes` fields (`describes_closed`) and `LoebSound` quantify `(V : Type)`.
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The probes against `.bot DefectBot`, found in every model: Guardian and Wary (Cupod is `cupod_botDB_V`) -/

section probes

lemma lMap_swap_gGT : Semiformula.lMap swap gGT = gG := by rw [← lMap_swap_gG, lMap_swap_swap]
lemma lMap_swap_gWT : Semiformula.lMap swap gWT = gW := by rw [← lMap_swap_gW, lMap_swap_swap]

/-- Guardian's guard against `.bot DefectBot`: "`.bot DefectBot` plays D against `.bot CooperateBot`" (a closed atom;
the me-slots inert). -/
noncomputable def qGB1 : Semisentence LAct 1 :=
  qT gG (TS gG 1) (uS gG 1) (wS gG 1) (cl TB0) (cterm Act.D) (cterm Act.C)

theorem guardCode_GB1 (k : V) :
    guardCode (⌜gG⌝ : V) (SV gG 1 k) (pBot (pConst 1)) = instB (⌜qGB1⌝ : V) k :=
  guardCode_qT_eq_instB gG k _ _ _ _ _ _ (hX_SV gG 1 (Or.inr rfl) k) (hU_SV gG 1 (Or.inr rfl) k)
    (hW_SV gG 1 (Or.inr rfl) k) (hX_bot_one k) hU_D_bot_one hW_C_bot_one

theorem tact_qGB1 : TAct ⊢ ∀¹ qGB1 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGB1, eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_one, progCode_bot, progCode_const, PD.Bots.CooperateBot, cast_pBot,
      cast_pConst, Nat.cast_zero]
    rw [val_desc_bot_one x]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGB1, eval_qT_swap, lMap_swap_gG, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_zero, progCode_bot, progCode_const, PD.Bots.DefectBot, cast_pBot,
      cast_pConst, Nat.cast_one]
    rw [val_desc_bot_zero x]
    exact bot_const_play_V _ _ _

/-- **Guardian defects against `.bot DefectBot` in every model, above a standard threshold** (fuel 2; the V-generic
`pos_GuardianBot_vs_botDB`). -/
theorem guardian_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gG 1 k) (pBot (pConst 1)) (SV gG 1 k) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qGB1
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gG 1 k (SV gG 1 k) (pBot (pConst 1)) (by rw [guardCode_GB1]; exact h V k hk)
  rwa [Nat.cast_one] at this

/-- The transposed Guardian's guard against `.bot CooperateBot`: "`.bot CooperateBot` plays C against `.bot DefectBot`". -/
noncomputable def qGTB0 : Semisentence LAct 1 :=
  qT gGT (TS gGT 0) (uS gGT 0) (wS gGT 0) (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_GTB0 (k : V) :
    guardCode (⌜gGT⌝ : V) (SV gGT 0 k) (pBot (pConst 0)) = instB (⌜qGTB0⌝ : V) k :=
  guardCode_qT_eq_instB gGT k _ _ _ _ _ _ (hX_SV gGT 0 (Or.inl rfl) k) (hU_SV gGT 0 (Or.inl rfl) k)
    (hW_SV gGT 0 (Or.inl rfl) k) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qGTB0 : TAct ⊢ ∀¹ qGTB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGTB0, eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_zero, progCode_bot, progCode_const, PD.Bots.DefectBot, cast_pBot,
      cast_pConst, Nat.cast_one]
    rw [val_desc_bot_zero x]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGTB0, eval_qT_swap, lMap_swap_gGT, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_one, progCode_bot, progCode_const, PD.Bots.CooperateBot, cast_pBot,
      cast_pConst, Nat.cast_zero]
    rw [val_desc_bot_one x]
    exact bot_const_play_V _ _ _

/-- **The transposed Guardian cooperates with `.bot CooperateBot` in every model, above a standard threshold** (fuel 2). -/
theorem guardianT_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gGT 0 k) (pBot (pConst 0)) (SV gGT 0 k) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qGTB0
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gGT 0 k (SV gGT 0 k) (pBot (pConst 0)) (by rw [guardCode_GTB0]; exact h V k hk)
  rwa [Nat.cast_zero] at this

/-- **Wary defects against `.bot DefectBot` in every model, above a standard threshold** (fuel 2; the V-generic
`pos_WaryBot_vs_botDB`: its `.neg` guard is a Π₁ truth by determinism, `tact_qWB1`). -/
theorem wary_botDB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gW 1 k) (pBot (pConst 1)) (SV gW 1 k) 1 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qWB1
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gW 1 k (SV gW 1 k) (pBot (pConst 1)) (by rw [guardCode_WB1]; exact h V k hk)
  rwa [Nat.cast_one] at this

/-- The transposed Wary's guard against `.bot CooperateBot`: "`.bot CooperateBot` does NOT play D against τWary(k)". -/
noncomputable def qWTB0 : Semisentence LAct 1 :=
  qT gWT (TS gWT 0) (uS gWT 0) (wS gWT 0) (cl TB0) (cterm Act.C) (cterm Act.D)

theorem guardCode_WTB0 (k : V) :
    guardCode (⌜gWT⌝ : V) (SV gWT 0 k) (pBot (pConst 0)) = instB (⌜qWTB0⌝ : V) k :=
  guardCode_qT_eq_instB gWT k _ _ _ _ _ _ (hX_SV gWT 0 (Or.inl rfl) k) (hU_SV gWT 0 (Or.inl rfl) k)
    (hW_SV gWT 0 (Or.inl rfl) k) (hX_bot_zero k) hU_C_bot_zero hW_D_bot_zero

theorem tact_qWTB0 : TAct ⊢ ∀¹ qWTB0 := by
  refine tact_all_of_both _ (fun M _ _ x ↦ ?_) (fun M _ _ x ↦ ?_)
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWTB0, eval_qT_neg_plays_opp_self .D _ _ _ _ _ _ x (desc_SV gWT 0 (Or.inl rfl) x) (val_desc_bot_zero x),
      actCode_D_cast]
    exact bot_const_not_play_V _ _ _root_.zero_ne_one
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qWTB0, eval_qT_swap, lMap_swap_gWT, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_neg_plays_opp_self .C _ _ _ _ _ _ x (descT_SV gWT 0 (Or.inl rfl) x) (val_desc_bot_one x),
      actCode_C_cast]
    exact bot_const_not_play_V _ _ _root_.one_ne_zero

/-- **The transposed Wary cooperates with `.bot CooperateBot` in every model, above a standard threshold** (fuel 2). -/
theorem waryT_botCB_V :
    ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV gWT 0 k) (pBot (pConst 0)) (SV gWT 0 k) 0 := by
  obtain ⟨kHat, h⟩ := found_of_all_V tact_qWTB0
  refine ⟨kHat, fun V _ _ k hk ↦ ?_⟩
  have := SV_then_V gWT 0 k (SV gWT 0 k) (pBot (pConst 0)) (by rw [guardCode_WTB0]; exact h V k hk)
  rwa [Nat.cast_zero] at this

end probes

/-! ### 2. The prudence guard against an engine searcher as a fixed formula, and the `k̂`-chain -/

section prudenceChain

/-- **Prudent's prudence guard against the engine searcher `SV g a k`, as a fixed formula**: "`SV g a k` plays D
against `.bot DefectBot`" — Prudent described above `KP` by `(TP, uP, wP)` (inert), the opponent by its canonical
`SV` triple. -/
noncomputable def qPiS (g : Semisentence LAct 6) (a : ℕ) : Semisentence LAct 1 :=
  qT templateP2 TP uP wP (TS g a) (uS g a) (wS g a)

/-- The instance equation on codes (above `KP`). -/
theorem guardCode_PiS (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜templateP2⌝ : V) (PrudentV k) (SV g a k) = instB (⌜qPiS g a⌝ : V) k :=
  guardCode_qT_eq_instB templateP2 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_SV g a ha k) (hU_SV g a ha k) (hW_SV g a ha k)

/-- `qPiS g a (k)` in the standard reading: `SV g a k` plays D against `pBot (pConst 1)` (no threshold: the me-slots
are inert). -/
theorem eval_qPiS_iff_V (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qPiS g a) ↔
      ∃ n, EvalGraph n (SV g a k) (pBot (pConst 1)) (SV g a k) 1 := by
  unfold qPiS templateP2 phiP2
  rw [eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, progCode_bot, progCode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst]
  rw [desc_SV g a ha k]

/-- `qPiS g a (k)` in the swapped reading: the transposed searcher plays C against `pBot (pConst 0)`. -/
theorem eval_qPiS_swap_iff_V (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qPiS g a) ↔
      ∃ n, EvalGraph n (SV (Semiformula.lMap swap g) (1 - a) k) (pBot (pConst 0))
        (SV (Semiformula.lMap swap g) (1 - a) k) 0 := by
  unfold qPiS
  rw [eval_qT_swap, lMap_swap_templateP2]
  unfold templateP2T
  rw [eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, progCode_bot, progCode_const, cast_pBot, cast_pConst]
  rw [descT_SV g a ha k]

/-- **The uniform theorem of the prudence guard** for a searcher whose defection against `.bot DefectBot` (and whose
transposition's cooperation with `.bot CooperateBot`) holds in every model above a threshold:
`TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 qPiS g a)`, by completeness. -/
theorem tact_qPiS_above (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
    (hD : ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV g a k) (pBot (pConst 1)) (SV g a k) 1)
    (hDT : ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV (Semiformula.lMap swap g) (1 - a) k) (pBot (pConst 0))
        (SV (Semiformula.lMap swap g) (1 - a) k) 0) :
    ∃ kHat : ℕ, TAct ⊢ ∀¹ ((leF (↑kHat) #0 : Semisentence LAct 1) 🡒 qPiS g a) := by
  obtain ⟨k₁, h₁⟩ := hD
  obtain ⟨k₂, h₂⟩ := hDT
  refine ⟨k₁ + k₂, tact_all_above_of_both _ _ (fun M _ _ x hx ↦ ?_) (fun M _ _ x hx ↦ ?_)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_qPiS_iff_V g a ha]
    exact ⟨_, h₁ M x (le_trans (by push_cast; exact le_self_add) hx)⟩
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [eval_qPiS_swap_iff_V g a ha]
    exact ⟨_, h₂ M x (le_trans (by push_cast; exact le_add_self) hx)⟩

/-- **The prudence guard against an engine searcher is FOUND for all large `k`** (the `k̂`-chain, on the arith codes):
`found_of_all_above` on `qPiS g a`, the instance equation above `KP`. -/
theorem prudence_found_of_SV (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1)
    (hD : ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV g a k) (pBot (pConst 1)) (SV g a k) 1)
    (hDT : ∃ kHat : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V), (kHat : V) ≤ k →
      EvalGraph 2 (SV (Semiformula.lMap swap g) (1 - a) k) (pBot (pConst 0))
        (SV (Semiformula.lMap swap g) (1 - a) k) 0) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜templateP2⌝ : ℕ) (Prudent k) (SV (V := ℕ) g a k)) := by
  obtain ⟨kHat, hq⟩ := tact_qPiS_above g a ha hD hDT
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq (fun k ↦ instB (⌜qPiS g a⌝ : ℕ) k) (fun _ ↦ rfl)
  refine ⟨k₀ + KP, fun k hk ↦ ?_⟩
  rw [← PrudentV_nat,
    guardCode_PiS g a ha (k := k) (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))]
  exact h k (by omega)

/-- The prudence template is the code of `phiPi` (the engine's stored template). -/
lemma templateCode_phiPi : templateCode phiPi = (⌜templateP2⌝ : ℕ) := templateCode_eq_quote_template phiPi rfl

/-- **Prudent's prudence guard against `GuardianBot k` is FOUND for all large `k`**: Guardian's defection against
`.bot DefectBot` is its then-branch on a true closed atom, in every model above a threshold. -/
theorem prudence_found_vs_GuardianBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (GuardianBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gG 1 (Or.inr rfl) guardian_botDB_V
    (by rw [lMap_swap_gG]; exact guardianT_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_PrudentBot, progCode_GuardianBot_SV, templateCode_phiPi]
  exact h k hk

/-- **Prudent's prudence guard against `WaryBot k` is FOUND for all large `k`**: Wary's defection against
`.bot DefectBot` is its then-branch on the Π₁ truth "`.bot DefectBot` does not cooperate with me". -/
theorem prudence_found_vs_WaryBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (WaryBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gW 1 (Or.inr rfl) wary_botDB_V
    (by rw [lMap_swap_gW]; exact waryT_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_PrudentBot, progCode_WaryBot_SV, templateCode_phiPi]
  exact h k hk

/-- **Prudent's prudence guard against `CupodBot k` is FOUND for all large `k`**: Cupod's defection against
`.bot DefectBot` is its then-branch on the true atom "`.bot DefectBot` defects against me". -/
theorem prudence_found_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiPi) (progCode (PrudentBot k)) (progCode (CupodBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gCu 1 (Or.inr rfl) cupod_botDB_V
    (by rw [lMap_swap_gCu]; exact dupoc_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_PrudentBot, progCode_CupodBot_SV, templateCode_phiPi]
  exact h k hk

end prudenceChain

/-! ### 3. The three dichotomies restated with the prudence hinge discharged -/

section restated

/-- **Guardian × Prudent** (engine `llm_outcome_GuardianBot_vs_PrudentBot = (C, D)`, pad 3), the prudence hinge
discharged: two hinges, NESTED — `G` = Guardian's guard "Prudent plays D against `.bot CooperateBot`" (outer split),
then Prudent's outer guard `A` "Guardian plays C against me". `G ⇒ (D, D)`; `¬G ⇒` Guardian C, `¬A ⇒` Prudent D (the
engine's world), `A ⇒` Prudent C. -/
theorem dich_GuardianBot_vs_PrudentBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiG) (progCode (GuardianBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (GuardianBot k)) (progCode (PrudentBot k)) (progCode (GuardianBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiG) (progCode (GuardianBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (GuardianBot k)) (progCode (PrudentBot k)) (progCode (GuardianBot k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (GuardianBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (GuardianBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_GuardianBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_GuardianBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hG, hn⟩ := h₁ k (by omega)
  refine ⟨hG, fun h ↦ ?_⟩
  obtain ⟨hGC, hPD, hPC⟩ := hn h
  exact ⟨hGC, fun hA ↦ hPD (Or.inl hA), fun hA ↦ hPC hA (by simp only [hingeB phiPi]; exact hB k (by omega))⟩

/-- **Wary × Prudent** (engine `llm_outcome_WaryBot_vs_PrudentBot = (C, D)`, pad 3), the prudence hinge discharged:
two hinges, NESTED — Prudent's outer guard `A` "Wary plays C against me" (outer split), then `W` = Wary's `.neg` guard
"¬(Prudent plays C against me)". `A ⇒ (C, C)`; `¬A ⇒` Prudent D, `W ⇒` Wary D, `¬W ⇒` Wary C (the engine's world). -/
theorem dich_WaryBot_vs_PrudentBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) →
        EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .C) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (WaryBot k)) (progCode (PrudentBot k)) (actCode .C)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (WaryBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (WaryBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        (LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (PrudentBot k)) k) →
          EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .D)) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiW) (progCode (WaryBot k)) (progCode (PrudentBot k)) k) →
          EvalGraph 3 (progCode (WaryBot k)) (progCode (PrudentBot k)) (progCode (WaryBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_WaryBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_WaryBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hAB, hn⟩ := h₁ k (by omega)
  exact ⟨fun hA ↦ hAB hA (by simp only [hingeB phiPi]; exact hB k (by omega)), fun hA ↦ hn (Or.inl hA)⟩

/-- **Cupod × Prudent** (engine `outcome_CupodBot_vs_PrudentBot = (C, D)`, pad 3), the prudence hinge discharged:
two hinges, NESTED — `Cu` = Cupod's guard "Prudent plays D against me" (outer split), then Prudent's outer guard `A`
"Cupod plays C against me". `Cu ⇒ (D, D)`; `¬Cu ⇒` Cupod C, `¬A ⇒` Prudent D (the engine's world), `A ⇒` Prudent C. -/
theorem dich_CupodBot_vs_PrudentBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_CupodBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_CupodBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hCu, hn⟩ := h₁ k (by omega)
  refine ⟨hCu, fun h ↦ ?_⟩
  obtain ⟨hCC, hPD, hPC⟩ := hn h
  exact ⟨hCC, fun hA ↦ hPD (Or.inl hA), fun hA ↦ hPC hA (by simp only [hingeB phiPi]; exact hB k (by omega))⟩

/-- **Prudent × Cupod** (engine `outcome_PrudentBot_vs_CupodBot = (D, C)`, pad 3): the same pair, Prudent's side first,
the prudence hinge discharged. -/
theorem dich_PrudentBot_vs_CupodBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .D)) ∧
      (¬ LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (PrudentBot k)) k) →
        EvalGraph 3 (progCode (CupodBot k)) (progCode (PrudentBot k)) (progCode (CupodBot k)) (actCode .C) ∧
        (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .D)) ∧
        (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode (CupodBot k)) k) →
          EvalGraph 3 (progCode (PrudentBot k)) (progCode (CupodBot k)) (progCode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₀, h⟩ := dich_CupodBot_vs_PrudentBot_prudenceFound
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨h1, h2⟩ := h k hk
  exact ⟨fun hCu ↦ ⟨(h1 hCu).2, (h1 hCu).1⟩, h2⟩

end restated

/-! ### 4. Prudent × `.bot MirrorBot` by Löb: `Cells/PrudentMirror`'s family at the closed opponent `pBot Mirror` -/

section botMirror

/-! #### The closed opponent, its description, its copy step -/

lemma cast_botMirror : ((pBot Mirror : ℕ) : V) = pBot MirrorV := by rw [cast_pBot, cast_Mirror]

lemma transposeCode_botMirrorV : transposeCode (pBot (MirrorV : V)) = pBot MirrorV := by rw [transposeCode_pBot, transposeCode_MirrorV]

lemma hX_botMirror (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V))
      (⌜(Rew.emb (cl (canonicalMeta (pBot Mirror)) : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (pBot MirrorV)) := by
  have := (describes_closed (pBot Mirror)).hX V k
  rwa [descVal_closed, cast_botMirror] at this

lemma hU_botMirror (k : V) : (⌜revalueUMeta (pBot Mirror)⌝ : V) = revalueU (pBot MirrorV) := by
  have := (describes_closed (pBot Mirror)).hU V k
  rwa [descVal_closed, cast_botMirror] at this

lemma hW_botMirror (k : V) : (⌜revalueWMeta (pBot Mirror)⌝ : V) = revalueW (pBot MirrorV) := by
  have := (describes_closed (pBot Mirror)).hW V k
  rwa [descVal_closed, cast_botMirror] at this

/-- The closed triple denotes `pBot MirrorV` (values). -/
lemma desc_botMirror (k : V) :
    revalue ((revalueUMeta (pBot Mirror)).val (s := stdReadingV V) ![] Empty.elim) ((revalueWMeta (pBot Mirror)).val (s := stdReadingV V) ![] Empty.elim)
      ((cl (canonicalMeta (pBot Mirror)) : Semiterm LAct Empty 1).val (s := stdReadingV V) ![k] Empty.elim) = pBot MirrorV := by
  have h := descVal_closed (V := V) (pBot Mirror) k
  rwa [descVal_def, cast_botMirror] at h

/-- The transposed closed triple denotes `pBot MirrorV` too (Mirror is τ-fixed). -/
lemma descT_botMirror (k : V) :
    revalue ((Semiterm.lMap swap (revalueUMeta (pBot Mirror))).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (revalueWMeta (pBot Mirror))).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cl (canonicalMeta (pBot Mirror)) : Semiterm LAct Empty 1)).val (s := stdReadingV V) ![k] Empty.elim) =
      pBot MirrorV := by
  have h := descVal_closed_T (V := V) (pBot Mirror) k
  rwa [descVal_def, cast_botMirror, transposeCode_botMirrorV] at h

/-- **`.bot MirrorBot`'s step in every model**: the `.bot` unwrapping and Mirror's sim step — `pBot MirrorV` in the
frame `(pBot MirrorV, opp)` runs `opp` in the frame `(opp, pBot MirrorV)`, two fuels more. -/
theorem botMirror_step_V (n opp a : V) :
    EvalGraph (n + 1 + 1) (pBot MirrorV) opp (pBot MirrorV) a ↔ EvalGraph n opp (pBot MirrorV) opp a := by
  rw [EvalGraph.bot_iff]
  have h := EvalGraph.sim_iff (n := n) (me := pBot (MirrorV : V)) (opp := opp) (p := pOpp) (q := pSelf) (a := a)
  rw [substCode_opp, substCode_self] at h
  exact h

/-- `.bot MirrorBot` copies a fuel-3 play at fuel 5. -/
theorem botMirror_copies3_V (opp a : V) (h : EvalGraph 3 opp (pBot MirrorV) opp a) :
    EvalGraph 5 (pBot MirrorV) opp (pBot MirrorV) a := by
  rw [show (5 : V) = 3 + 1 + 1 by norm_num]
  exact (botMirror_step_V 3 opp a).mpr h

/-- **The prudence fact for `.bot MirrorBot` in every model**: it plays D against `.bot DefectBot` (fuel 4). -/
theorem botMirror_botDB_V : EvalGraph 4 (pBot MirrorV) (pBot (pConst 1)) (pBot (MirrorV : V)) 1 := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 1)) (pBot MirrorV) (pConst 1) (1 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (pBot (pConst 1)) (pBot MirrorV) (pBot (pConst 1)) (1 : V) :=
    EvalGraph.bot_iff.mpr e0
  have e2 := (botMirror_step_V (0 + 1 + 1) (pBot (pConst 1)) 1).mpr e1
  rwa [show (0 : V) + 1 + 1 + 1 + 1 = 4 by norm_num] at e2

/-- The transposed prudence fact: `.bot MirrorBot` plays C against `.bot CooperateBot` (fuel 4). -/
theorem botMirror_botCB_V : EvalGraph 4 (pBot MirrorV) (pBot (pConst 0)) (pBot (MirrorV : V)) 0 := by
  have e0 : EvalGraph (0 + 1) (pBot (pConst 0)) (pBot MirrorV) (pConst 0) (0 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (pBot (pConst 0)) (pBot MirrorV) (pBot (pConst 0)) (0 : V) :=
    EvalGraph.bot_iff.mpr e0
  have e2 := (botMirror_step_V (0 + 1 + 1) (pBot (pConst 0)) 0).mpr e1
  rwa [show (0 : V) + 1 + 1 + 1 + 1 = 4 by norm_num] at e2

/-- Prudent's search clause against ANY opponent (fuel 3): both guards provable within `k` ⇒ `C`
(`prudent_search_V` with the opponent free). -/
theorem prudent_search_any_V (k opp : V)
    (h1 : LenBox TAct k (guardCode (⌜templateP1⌝ : V) (PrudentV k) opp))
    (h2 : LenBox TAct k (guardCode (⌜templateP2⌝ : V) (PrudentV k) opp)) :
    EvalGraph 3 (PrudentV k) opp (PrudentV k) 0 := by
  have e0 : EvalGraph (0 + 1) (PrudentV k) opp (pConst 0) (0 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (PrudentV k) opp (pSearch k (⌜templateP2⌝ : V) (pConst 0) (pConst 1)) 0 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ templateP2)).mpr (Or.inl ⟨h2, e0⟩)
  have e2 : EvalGraph (0 + 1 + 1 + 1) (PrudentV k) opp
      (pSearch k (⌜templateP1⌝ : V) (pSearch k (⌜templateP2⌝ : V) (pConst 0) (pConst 1)) (pConst 1)) 0 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ templateP1)).mpr (Or.inl ⟨h1, e1⟩)
  rwa [show (0 : V) + 1 + 1 + 1 = 3 by norm_num] at e2

/-- The transposed searcher's search clause against ANY opponent (fuel 3): both guards ⇒ `D`. -/
theorem prudentT_search_any_V (k opp : V)
    (h1 : LenBox TAct k (guardCode (⌜templateP1T⌝ : V) (PrudentTV k) opp))
    (h2 : LenBox TAct k (guardCode (⌜templateP2T⌝ : V) (PrudentTV k) opp)) :
    EvalGraph 3 (PrudentTV k) opp (PrudentTV k) 1 := by
  have e0 : EvalGraph (0 + 1) (PrudentTV k) opp (pConst 1) (1 : V) := EvalGraph.const_iff.mpr rfl
  have e1 : EvalGraph (0 + 1 + 1) (PrudentTV k) opp (pSearch k (⌜templateP2T⌝ : V) (pConst 1) (pConst 0)) 1 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ templateP2T)).mpr (Or.inl ⟨h2, e0⟩)
  have e2 : EvalGraph (0 + 1 + 1 + 1) (PrudentTV k) opp
      (pSearch k (⌜templateP1T⌝ : V) (pSearch k (⌜templateP2T⌝ : V) (pConst 1) (pConst 0)) (pConst 0)) 1 :=
    (EvalGraph.search_iff₆ (isSemiformula_quote₆ templateP1T)).mpr (Or.inl ⟨h1, e1⟩)
  rwa [show (0 : V) + 1 + 1 + 1 = 3 by norm_num] at e2

/-! #### The four fixed formulas: instance equations and truth equations -/

/-- **The outer fixed formula**: `qPB1(k)` says "`.bot MirrorBot` plays C against `PrudentV k`". -/
noncomputable def qPB1 : Semisentence LAct 1 :=
  qT templateP1 TP uP wP (cl (canonicalMeta (pBot Mirror))) (revalueUMeta (pBot Mirror)) (revalueWMeta (pBot Mirror))
/-- **The prudence fixed formula**: `qPB2(k)` says "`.bot MirrorBot` plays D against `.bot DefectBot`" (the
me-slots inert: a closed Σ₁ fact carried at every `k`). -/
noncomputable def qPB2 : Semisentence LAct 1 :=
  qT templateP2 TP uP wP (cl (canonicalMeta (pBot Mirror))) (revalueUMeta (pBot Mirror)) (revalueWMeta (pBot Mirror))
/-- The transposed outer formula: "`.bot MirrorBot` plays D against `PrudentTV k`". -/
noncomputable def qPB1T : Semisentence LAct 1 := Semiformula.lMap swap qPB1
/-- The transposed prudence formula: "`.bot MirrorBot` plays C against `.bot CooperateBot`". -/
noncomputable def qPB2T : Semisentence LAct 1 := Semiformula.lMap swap qPB2

lemma lMap_swap_qPB1 : Semiformula.lMap swap qPB1 = qPB1T := rfl
lemma lMap_swap_qPB2 : Semiformula.lMap swap qPB2 = qPB2T := rfl

/-- The instance equation on codes (above `KP`): Prudent's outer guard code against `.bot MirrorBot` is the
`binNumeral k`-instance of `⌜qPB1⌝`. -/
theorem guardCode_PB1 {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜templateP1⌝ : V) (PrudentV k) (pBot MirrorV) = instB (⌜qPB1⌝ : V) k :=
  guardCode_qT_eq_instB templateP1 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_botMirror k) (hU_botMirror k) (hW_botMirror k)

/-- The prudence guard code is the `binNumeral k`-instance of `⌜qPB2⌝`. -/
theorem guardCode_PB2 {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜templateP2⌝ : V) (PrudentV k) (pBot MirrorV) = instB (⌜qPB2⌝ : V) k :=
  guardCode_qT_eq_instB templateP2 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_botMirror k) (hU_botMirror k) (hW_botMirror k)

/-- The transposed searcher's outer guard code against `.bot MirrorBot` is the `binNumeral k`-instance of `⌜qPB1T⌝`. -/
theorem guardCode_PB1T {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜templateP1T⌝ : V) (PrudentTV k) (pBot MirrorV) = instB (⌜qPB1T⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB templateP1 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_botMirror k) (hU_botMirror k) (hW_botMirror k)
  rw [lMap_swap_templateP1, transposeCode_PrudentV, transposeCode_botMirrorV] at h
  exact h

theorem guardCode_PB2T {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜templateP2T⌝ : V) (PrudentTV k) (pBot MirrorV) = instB (⌜qPB2T⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB templateP2 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_botMirror k) (hU_botMirror k) (hW_botMirror k)
  rw [lMap_swap_templateP2, transposeCode_PrudentV, transposeCode_botMirrorV] at h
  exact h

/-- `qPB1(k)` holds in `stdReadingV V` iff `.bot MirrorBot` plays C against `PrudentV k` (above the threshold). -/
theorem eval_qPB1_iff_V {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qPB1 ↔
      ∃ n, EvalGraph n (pBot MirrorV) (PrudentV k) (pBot MirrorV) 0 := by
  unfold qPB1 templateP1 phiP1
  rw [eval_qT_plays_opp_self .C _ _ _ _ _ _ k (descVal_prudent hk) (descVal_closed (pBot Mirror) k), actCode_C_cast,
    cast_botMirror]

/-- `qPB2(k)` holds in `stdReadingV V` iff `.bot MirrorBot` plays D against `.bot DefectBot`. -/
theorem eval_qPB2_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qPB2 ↔
      ∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 1)) (pBot (MirrorV : V)) 1 := by
  unfold qPB2 templateP2 phiP2
  rw [eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, progCode_bot, progCode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst]
  rw [desc_botMirror k]

/-- `qPB1T(k)` holds in `stdReadingV V` iff `.bot MirrorBot` plays D against `PrudentTV k`. -/
theorem eval_qPB1T_iff_V {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qPB1T ↔
      ∃ n, EvalGraph n (pBot MirrorV) (PrudentTV k) (pBot MirrorV) 1 := by
  unfold qPB1T qPB1
  rw [lMap_swap_qT, lMap_swap_templateP1]
  unfold templateP1T
  rw [eval_qT_plays_opp_self .D _ _ _ _ _ _ k (descVal_prudent_T hk) (descVal_closed_T (pBot Mirror) k), actCode_D_cast,
    cast_botMirror, transposeCode_botMirrorV]

/-- `qPB2T(k)` holds in `stdReadingV V` iff `.bot MirrorBot` plays C against `.bot CooperateBot`. -/
theorem eval_qPB2T_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qPB2T ↔
      ∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 0)) (pBot (MirrorV : V)) 0 := by
  unfold qPB2T qPB2
  rw [lMap_swap_qT, lMap_swap_templateP2]
  unfold templateP2T
  rw [eval_qT_iff, eval_template_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, progCode_bot, progCode_const, cast_pBot, cast_pConst]
  rw [descT_botMirror k]

/-! #### The family, its Löb premise -/

/-- Prudent's half of the family: the outer guard and the prudence guard. -/
noncomputable def pPBa : Semisentence LAct 1 := qPB1 ⋏ qPB2
/-- The transposed searcher's half. -/
noncomputable def pPBb : Semisentence LAct 1 := qPB1T ⋏ qPB2T
/-- **The Löb family of the Prudent × `.bot MirrorBot` cell**: `pPM`'s shape at the closed opponent. -/
noncomputable def pPB : Semisentence LAct 1 := pPBa ⋏ pPBb

lemma pPBa_def : pPBa = qPB1 ⋏ qPB2 := rfl
lemma pPBb_def : pPBb = qPB1T ⋏ qPB2T := rfl
lemma pPB_def : pPB = pPBa ⋏ pPBb := rfl

lemma lMap_swap_pPBa : Semiformula.lMap swap pPBa = pPBb := by
  rw [pPBa_def, pPBb_def, LogicalConnective.HomClass.map_and, lMap_swap_qPB1, lMap_swap_qPB2]
lemma lMap_swap_pPBb : Semiformula.lMap swap pPBb = pPBa := by
  rw [← lMap_swap_pPBa, lMap_swap_swap]
lemma lMap_swap_pPB : Semiformula.lMap swap pPB = pPBb ⋏ pPBa := by
  rw [pPB_def, LogicalConnective.HomClass.map_and, lMap_swap_pPBa, lMap_swap_pPBb]

theorem instB_quote_pPBa (k : V) :
    instB (⌜pPBa⌝ : V) k = instB (⌜qPB1⌝ : V) k ^⋏ instB (⌜qPB2⌝ : V) k := instB_quote_and _ _ k
theorem instB_quote_pPBb (k : V) :
    instB (⌜pPBb⌝ : V) k = instB (⌜qPB1T⌝ : V) k ^⋏ instB (⌜qPB2T⌝ : V) k := instB_quote_and _ _ k
theorem instB_quote_pPB (k : V) :
    instB (⌜pPB⌝ : V) k = instB (⌜pPBa⌝ : V) k ^⋏ instB (⌜pPBb⌝ : V) k := instB_quote_and _ _ k

lemma formulaLen_instB_pPBa (k : V) :
    formulaLen LAct (instB (⌜pPBa⌝ : V) k) =
      formulaLen LAct (instB (⌜qPB1⌝ : V) k) + formulaLen LAct (instB (⌜qPB2⌝ : V) k) + 1 := by
  rw [instB_quote_pPBa,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pPBb (k : V) :
    formulaLen LAct (instB (⌜pPBb⌝ : V) k) =
      formulaLen LAct (instB (⌜qPB1T⌝ : V) k) + formulaLen LAct (instB (⌜qPB2T⌝ : V) k) + 1 := by
  rw [instB_quote_pPBb,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]
lemma formulaLen_instB_pPB (k : V) :
    formulaLen LAct (instB (⌜pPB⌝ : V) k) =
      formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k) + 1 := by
  rw [instB_quote_pPB,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both searchers play from a box of the family** (fuel 3): the two-level ∧-elimination hands each searcher
BOTH its guards against `.bot MirrorBot`. -/
theorem pPB_all_V (k a : V) (hk : (KP : V) ≤ k)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPB1⌝ : V) k) + formulaLen LAct (instB (⌜qPB2⌝ : V) k)) + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPB1T⌝ : V) k) + formulaLen LAct (instB (⌜qPB2T⌝ : V) k)) + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pPB⌝ : V) k)) :
    EvalGraph 3 (PrudentV k) (pBot MirrorV) (PrudentV k) 0 ∧ EvalGraph 3 (PrudentTV k) (pBot MirrorV) (PrudentTV k) 1 := by
  rw [instB_quote_pPB] at h
  have hx := isFormula_instB_quote pPBa k
  have hy := isFormula_instB_quote pPBb k
  have h₁ : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7)
      (instB (⌜qPB1⌝ : V) k ^⋏ instB (⌜qPB2⌝ : V) k) := by
    rw [← instB_quote_pPBa]; exact lenBoxUnbounded_andL_V hx hy h
  have h₂ : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7)
      (instB (⌜qPB1T⌝ : V) k ^⋏ instB (⌜qPB2T⌝ : V) k) := by
    rw [← instB_quote_pPBb]; exact lenBoxUnbounded_andR_V hx hy h
  have hx₁ := isFormula_instB_quote qPB1 k
  have hy₁ := isFormula_instB_quote qPB2 k
  have hx₂ := isFormula_instB_quote qPB1T k
  have hy₂ := isFormula_instB_quote qPB2T k
  have g1 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andL_V hx₁ hy₁ h₁)
  have g2 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andR_V hx₁ hy₁ h₁)
  have g3 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx₂ hy₂ h₂)
  have g4 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx₂ hy₂ h₂)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB1 hk] at g1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB2 hk] at g2
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB1T hk] at g3
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB2T hk] at g4
  exact ⟨prudent_search_any_V k _ g1 g2, prudentT_search_any_V k _ g3 g4⟩

/-- **The box form**: Prudent's two guards against `.bot MirrorBot` are provable within `k`. -/
theorem pPB_guards_V (k a : V) (hk : (KP : V) ≤ k)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qPB1⌝ : V) k) + formulaLen LAct (instB (⌜qPB2⌝ : V) k)) + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pPB⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateP1⌝ : V) (PrudentV k) (pBot MirrorV)) ∧
    LenBox TAct k (guardCode (⌜templateP2⌝ : V) (PrudentV k) (pBot MirrorV)) := by
  rw [instB_quote_pPB] at h
  have hx := isFormula_instB_quote pPBa k
  have hy := isFormula_instB_quote pPBb k
  have h₁ : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pPBa⌝ : V) k) + formulaLen LAct (instB (⌜pPBb⌝ : V) k)) + 7)
      (instB (⌜qPB1⌝ : V) k ^⋏ instB (⌜qPB2⌝ : V) k) := by
    rw [← instB_quote_pPBa]; exact lenBoxUnbounded_andL_V hx hy h
  have hx₁ := isFormula_instB_quote qPB1 k
  have hy₁ := isFormula_instB_quote qPB2 k
  have g1 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andL_V hx₁ hy₁ h₁)
  have g2 := lenBoxUnbounded_mono_V ha₁ (lenBoxUnbounded_andR_V hx₁ hy₁ h₁)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB1 hk] at g1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_PB2 hk] at g2
  exact ⟨g1, g2⟩

/-- `pPB(k)` in the standard reading (above the threshold). -/
theorem eval_pPB_iff_std {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pPB ↔
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentV k) (pBot MirrorV) 0) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 1)) (pBot (MirrorV : V)) 1)) ∧
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentTV k) (pBot MirrorV) 1) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 0)) (pBot (MirrorV : V)) 0)) := by
  rw [pPB_def, pPBa_def, pPBb_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qPB1_iff_V hk, eval_qPB2_iff_V, eval_qPB1T_iff_V hk, eval_qPB2T_iff_V]

/-- `pPB(k)` in the swapped reading: the SAME four facts (the halves exchange roles). -/
theorem eval_pPB_iff_swap {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pPB ↔
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentTV k) (pBot MirrorV) 1) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 0)) (pBot (MirrorV : V)) 0)) ∧
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentV k) (pBot MirrorV) 0) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 1)) (pBot (MirrorV : V)) 1)) := by
  rw [eval_swappedReading, lMap_swap_pPB, ← stdReadingV_eq_stdReading, pPBa_def, pPBb_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qPB1_iff_V hk, eval_qPB2_iff_V, eval_qPB1T_iff_V hk, eval_qPB2T_iff_V]

theorem eval_pPB_iff_stdReading {k : V} (hk : (KP : V) ≤ k) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pPB ↔
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentV k) (pBot MirrorV) 0) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 1)) (pBot (MirrorV : V)) 1)) ∧
      ((∃ n, EvalGraph n (pBot MirrorV) (PrudentTV k) (pBot MirrorV) 1) ∧
        (∃ n, EvalGraph n (pBot MirrorV) (pBot (pConst 0)) (pBot (MirrorV : V)) 0)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pPB_iff_std hk

/-- **The bounded Löb premise of the Prudent × `.bot MirrorBot` family, slack `(14 + KP, 16)`**: a box of `pPB(k)`
with the slack makes both searchers play at fuel 3 (`pPB_all_V`), `.bot MirrorBot` copies at fuel 5, and the two
prudence facts hold outright — so `pPB(k)` is TRUE in both readings. -/
theorem loebSound_pPB : LoebSound pPB (14 + KP) 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (KP : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left KP 14)) (le_trans le_add_self (le_trans le_self_add ha))
  have h14 : ((14 : ℕ) : V) ≤ ((14 + KP : ℕ) : V) := Nat.cast_le.mpr (Nat.le_add_right 14 KP)
  have hb : a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * formulaLen LAct (instB (⌜pPB⌝ : V) k) ≤
      a + ((14 + KP : ℕ) : V) + ((16 : ℕ) : V) * formulaLen LAct (instB (⌜pPB⌝ : V) k) :=
    _root_.add_le_add_left (_root_.add_le_add_right h14 a) _
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pPBa k) (formulaLen_instB_pPB k)) (le_trans hb ha)
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pPBb k) (formulaLen_instB_pPB k)) (le_trans hb ha)
  obtain ⟨g1, g2⟩ := pPB_all_V k a hk ha₁ ha₂ h
  exact ⟨(eval_pPB_iff_stdReading hk).mpr
      ⟨⟨⟨5, botMirror_copies3_V _ _ g1⟩, ⟨4, botMirror_botDB_V⟩⟩, ⟨⟨5, botMirror_copies3_V _ _ g2⟩, ⟨4, botMirror_botCB_V⟩⟩⟩,
    (eval_pPB_iff_swap hk).mpr
      ⟨⟨⟨5, botMirror_copies3_V _ _ g2⟩, ⟨4, botMirror_botCB_V⟩⟩, ⟨⟨5, botMirror_copies3_V _ _ g1⟩, ⟨4, botMirror_botDB_V⟩⟩⟩⟩

/-! #### The cells at ℕ -/

/-- **The Prudent × `.bot MirrorBot` cell, packaged** (arith codes): for all large `k`, Prudent cooperates with
`pBot Mirror` and its transposition defects (fuel 3), and both of Prudent's guard boxes hold — `family_found pPB` at
`boundedInnerNec_sixteen`, then the two-level ∧-elimination. -/
theorem loeb_Prudent_vs_botMirror_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 3 (Prudent k) (pBot Mirror) (Prudent k) 0 ∧ EvalGraph 3 (PrudentT k) (pBot Mirror) (PrudentT k) 1) ∧
      (LenBox TAct k (guardCode (⌜templateP1⌝ : ℕ) (Prudent k) (pBot Mirror)) ∧
        LenBox TAct k (guardCode (⌜templateP2⌝ : ℕ) (Prudent k) (pBot Mirror))) := by
  obtain ⟨k₀, h⟩ := family_found pPB boundedInnerNec_sixteen loebSound_pPB
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pPBa (V := ℕ) k)
    (formulaLen_instB_pPB (V := ℕ) k) (by omega))
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pPBb (V := ℕ) k)
    (formulaLen_instB_pPB (V := ℕ) k) (by omega))
  refine ⟨pPB_all_V (V := ℕ) k a ?_ ha₁ ha₂ hpc, pPB_guards_V (V := ℕ) k a ?_ ha₁ hpc⟩ <;>
    (rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))

/-- **PrudentBot × `.bot MirrorBot` is `(C, C)` in PA-`S'`, unconditional, on the engine's code**: for all large `k`,
`PrudentBot k` cooperates with `.bot MirrorBot` (fuel 3: outer search, inner search, constant) and `.bot MirrorBot`
copies (fuel 5: the `.bot` step, the sim step, Prudent's 3) — the `S'` twin of the engine's `prudent_botmirror_coop`
(`Theorems/PrudentBot/vs_EBot.lean`). -/
theorem loeb_PrudentBot_vs_botMirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 3 (progCode (PrudentBot k)) (pBot Mirror) (progCode (PrudentBot k)) (actCode .C) ∧
      EvalGraph 5 (pBot Mirror) (progCode (PrudentBot k)) (pBot Mirror) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_Prudent_vs_botMirror_core
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [progCode_PrudentBot]
  exact ⟨(h k hk).1.1, botMirror_copies3_V (V := ℕ) _ _ (h k hk).1.1⟩


end botMirror

/-! ### 5. Prudent × EBot closed in both worlds -/

section ebot

/-- `EBot` cooperates with `x` when `x` defects against `.bot DefectBot` and `.bot CooperateBot` but cooperates with
`.bot MirrorBot` (its THIRD rung; the companion of `ebot_C_of_probes`/`ebot_D_of_probes_D`). -/
theorem ebot_C_of_probes3 {x n : ℕ} (h1 : EvalGraph n x (pBot (pConst 1)) x 1)
    (h2 : EvalGraph n x (pBot (pConst 0)) x 1) (h3 : EvalGraph n x (pBot Mirror) x 0) :
    EvalGraph (n + 1 + 1 + 1 + 1) (progCode EBot) x (progCode EBot) 0 := by
  simp only [EBot, CooperateBot, DefectBot, MirrorBot, progCode_ite, progCode_sim, progCode_opp, progCode_self, progCode_bot,
    progCode_const, actCode]
  rw [EvalGraph.ite_iff]
  refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
  · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
    exact EvalGraph.mono_le (by omega) h1
  · rw [EvalGraph.ite_iff]
    refine ⟨1, ?_, Or.inr ⟨by decide, ?_⟩⟩
    · rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
      exact EvalGraph.mono_le (by omega) h2
    · rw [EvalGraph.ite_iff]
      refine ⟨0, ?_, Or.inl ⟨rfl, const_play _ _ _ _⟩⟩
      rw [EvalGraph.sim_iff, substCode_opp, substCode_bot]
      exact h3

/-- **EBot cooperates with `PrudentBot k` for all large `k`** (the settled half of Prudent × EBot, pad 7): Prudent
defects against `.bot DefectBot` (rung 1) and `.bot CooperateBot` (rung 2) and cooperates with `.bot MirrorBot` (rung 3,
`loeb_PrudentBot_vs_botMirror`) — whatever its outer verdict against EBot itself. -/
theorem floor_PrudentBot_vs_EBot_right :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 7 (progCode EBot) (progCode (PrudentBot k)) (progCode EBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_PrudentBot_vs_botMirror
  refine ⟨k₀, fun k hk ↦ ?_⟩
  exact ebot_C_of_probes3 (EvalGraph.mono_le (by omega) (snd_PrudentBot_vs_botDB k)) (snd_PrudentBot_vs_botCB k)
    (h k hk).1

/-- **Prudent × EBot** (engine `outcome_PrudentBot_vs_EBot = (D, C)`, pad 7; the LOEB-FP cell), BOTH worlds. Hinge:
Prudent's outer guard `A_k` "EBot plays C against me" (TRUE through EBot's third rung; the prudence guard is FOUND,
`prudence_found_vs_EBot`). `¬A_k ⇒ (D, C)` — the engine's value, EBot's C now proved (`floor_PrudentBot_vs_EBot_right`);
`A_k ⇒ (C, C)`. `dich_PrudentBot_vs_EBot` stated only Prudent's side of the `¬A_k` world. -/
theorem dich_PrudentBot_vs_EBot_full :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (¬ LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode EBot) k) →
        EvalGraph 7 (progCode (PrudentBot k)) (progCode EBot) (progCode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 7 (progCode EBot) (progCode (PrudentBot k)) (progCode EBot) (actCode .C)) ∧
      (LenBox TAct k (guardCodeB (templateCode phiPo) (progCode (PrudentBot k)) (progCode EBot) k) →
        EvalGraph 7 (progCode (PrudentBot k)) (progCode EBot) (progCode (PrudentBot k)) (actCode .C) ∧
        EvalGraph 7 (progCode EBot) (progCode (PrudentBot k)) (progCode EBot) (actCode .C)) := by
  obtain ⟨k₁, h₁⟩ := dich_PrudentBot_vs_EBot
  obtain ⟨k₂, h₂⟩ := floor_PrudentBot_vs_EBot_right
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hn, hf⟩ := h₁ k (by omega)
  exact ⟨fun h ↦ ⟨hn h, h₂ k (by omega)⟩, hf⟩

end ebot

end ArithS

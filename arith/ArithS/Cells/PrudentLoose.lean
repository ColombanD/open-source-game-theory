import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Cells.PrudentLoose — the two Prudent loose ends: the prudence `k̂`-chain and Prudent × `.bot MirrorBot`

`Research/Notes/ROUTE_B_SCOPE.md` §6 (2026-09-27, "Prudent loose ends") and `ARITHMETIZED_S_RESULTS.md` "The floors
as dichotomies". `Cells/FloorDichotomy` left Prudent's PRUDENCE guard `B_k` — "the opponent defects against
`.bot DefectBot`" (`phiPi`) — as a hinge of its own in five nested dichotomies, and stated Prudent × EBot's `¬A` world
on Prudent's side only. This module settles what can be settled.

**(a) The prudence `k̂`-chain.** For an opponent that is an engine searcher `SV g a k` (a constant template, the budget
in the search slot), the prudence guard is the `bnum k`-instance of ONE fixed formula `qPiS g a` (Prudent described
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
are the truth halves). For Just there is the further §7 obstruction: `pcode (JustBot k)` stores a `k`-dependent
template, so no fixed formula has the prudence guard as its `bnum k`-instance at all. Both cells keep `B` as a hinge.

**(b) Prudent × `.bot MirrorBot` by Löb.** EBot's third rung asks "Prudent cooperates with `.bot MirrorBot`"; in the
engine this is `prudent_botmirror_coop` (`Theorems/PrudentBot/vs_EBot.lean`). Here it is `Cells/PrudentMirror`'s family
re-instantiated at the CLOSED opponent `pBot Mirror` (`describes_closed`): the fixed formulas `qPB1` ("`.bot MirrorBot`
plays C against `Prudent k`") and `qPB2` ("`.bot MirrorBot` plays D against `.bot DefectBot`", the prudence conjunct),
their τ-twins, the family `pPB = (qPB1 ⋏ qPB2) ⋏ (τqPB1 ⋏ τqPB2)` with `loebSound_pPB : LoebSound pPB (14 + KP) 16`
(the two-level ∧-elimination hands each searcher both its guards; `.bot MirrorBot` copies at fuel 5 — the `.bot`
unwrapping is one fuel more than Mirror's fuel 4, `botMirror_step_V`; the prudence facts `botMirror_botDB_V`/
`botMirror_botCB_V` at fuel 4), and `family_found`. **`loeb_PrudentBot_vs_botMirror`**: for all large `k`,
`EvalGraph 3 (pcode (PrudentBot k)) (pBot Mirror) (pcode (PrudentBot k)) C ∧ EvalGraph 5 (pBot Mirror) (pcode (PrudentBot k)) (pBot Mirror) C`
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
    rw [qGB1, eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_one, pcode_bot, pcode_const, PD.Bots.CooperateBot, cast_pBot,
      cast_pConst, Nat.cast_zero]
    rw [val_desc_bot_one x]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGB1, eval_qT_swap, lMap_swap_gG, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_zero, pcode_bot, pcode_const, PD.Bots.DefectBot, cast_pBot,
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
    rw [qGTB0, eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_zero, pcode_bot, pcode_const, PD.Bots.DefectBot, cast_pBot,
      cast_pConst, Nat.cast_one]
    rw [val_desc_bot_zero x]
    exact bot_const_play_V _ _ _
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    rw [qGTB0, eval_qT_swap, lMap_swap_gGT, lMap_swap_cl, lMap_swap_TB0, lMap_swap_cterm_C, lMap_swap_cterm_D,
      eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
    simp only [Matrix.cons_val, actCode, Nat.cast_one, pcode_bot, pcode_const, PD.Bots.CooperateBot, cast_pBot,
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
  qT tmplP2 TP uP wP (TS g a) (uS g a) (wS g a)

/-- The instance equation on codes (above `KP`). -/
theorem guardCode_PiS (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) {k : V} (hk : (KP : V) ≤ k) :
    guardCode (⌜tmplP2⌝ : V) (PrudentV k) (SV g a k) = instB (⌜qPiS g a⌝ : V) k :=
  guardCode_qT_eq_instB tmplP2 k TP uP wP _ _ _ (hX_prudent hk) (hU_prudent hk) (hW_prudent hk)
    (hX_SV g a ha k) (hU_SV g a ha k) (hW_SV g a ha k)

/-- `qPiS g a (k)` in the standard reading: `SV g a k` plays D against `pBot (pConst 1)` (no threshold: the me-slots
are inert). -/
theorem eval_qPiS_iff_V (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qPiS g a) ↔
      ∃ n, EvalGraph n (SV g a k) (pBot (pConst 1)) (SV g a k) 1 := by
  unfold qPiS tmplP2 phiP2
  rw [eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_one, pcode_bot, pcode_const, PD.Bots.DefectBot, cast_pBot,
    cast_pConst]
  rw [desc_SV g a ha k]

/-- `qPiS g a (k)` in the swapped reading: the transposed searcher plays C against `pBot (pConst 0)`. -/
theorem eval_qPiS_swap_iff_V (g : Semisentence LAct 6) (a : ℕ) (ha : a = 0 ∨ a = 1) (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (qPiS g a) ↔
      ∃ n, EvalGraph n (SV (Semiformula.lMap swap g) (1 - a) k) (pBot (pConst 0))
        (SV (Semiformula.lMap swap g) (1 - a) k) 0 := by
  unfold qPiS
  rw [eval_qT_swap, lMap_swap_tmplP2]
  unfold tmplP2T
  rw [eval_qT_iff, eval_tmpl_plays_opp_closed_V _ (by intro h; cases h) (by intro h; cases h)]
  simp only [Matrix.cons_val, actCode, Nat.cast_zero, pcode_bot, pcode_const, cast_pBot, cast_pConst]
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
      LenProvableV TAct k (guardCode (⌜tmplP2⌝ : ℕ) (Prudent k) (SV (V := ℕ) g a k)) := by
  obtain ⟨kHat, hq⟩ := tact_qPiS_above g a ha hD hDT
  obtain ⟨k₀, h⟩ := found_of_all_above kHat hq (fun k ↦ instB (⌜qPiS g a⌝ : ℕ) k) (fun _ ↦ rfl)
  refine ⟨k₀ + KP, fun k hk ↦ ?_⟩
  rw [← PrudentV_nat,
    guardCode_PiS g a ha (k := k) (by rw [natCast_nat]; exact le_def.mpr (Nat.eq_or_lt_of_le (by omega)))]
  exact h k (by omega)

/-- The prudence template is the code of `phiPi` (the engine's stored template). -/
lemma tcode_phiPi : tcode phiPi = (⌜tmplP2⌝ : ℕ) := rfl
/-- The outer template is the code of `phiPo`. -/
lemma tcode_phiPo : tcode phiPo = (⌜tmplP1⌝ : ℕ) := rfl

/-- **Prudent's prudence guard against `GuardianBot k` is FOUND for all large `k`**: Guardian's defection against
`.bot DefectBot` is its then-branch on a true closed atom, in every model above a threshold. -/
theorem prudence_found_vs_GuardianBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiPi) (pcode (PrudentBot k)) (pcode (GuardianBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gG 1 (Or.inr rfl) guardian_botDB_V
    (by rw [lMap_swap_gG]; exact guardianT_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [pcode_PrudentBot, pcode_GuardianBot_SV, tcode_phiPi]
  exact h k hk

/-- **Prudent's prudence guard against `WaryBot k` is FOUND for all large `k`**: Wary's defection against
`.bot DefectBot` is its then-branch on the Π₁ truth "`.bot DefectBot` does not cooperate with me". -/
theorem prudence_found_vs_WaryBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiPi) (pcode (PrudentBot k)) (pcode (WaryBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gW 1 (Or.inr rfl) wary_botDB_V
    (by rw [lMap_swap_gW]; exact waryT_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [pcode_PrudentBot, pcode_WaryBot_SV, tcode_phiPi]
  exact h k hk

/-- **Prudent's prudence guard against `CupodBot k` is FOUND for all large `k`**: Cupod's defection against
`.bot DefectBot` is its then-branch on the true atom "`.bot DefectBot` defects against me". -/
theorem prudence_found_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (tcode phiPi) (pcode (PrudentBot k)) (pcode (CupodBot k))) := by
  obtain ⟨k₀, h⟩ := prudence_found_of_SV gCu 1 (Or.inr rfl) cupod_botDB_V
    (by rw [lMap_swap_gCu]; exact dupoc_botCB_V)
  refine ⟨k₀, fun k hk ↦ ?_⟩
  rw [pcode_PrudentBot, pcode_CupodBot_SV, tcode_phiPi]
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
      (LenProvableV TAct k (guardCodeB (tcode phiG) (pcode (GuardianBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (GuardianBot k)) (pcode (PrudentBot k)) (pcode (GuardianBot k)) (actCode .D) ∧
        EvalGraph 3 (pcode (PrudentBot k)) (pcode (GuardianBot k)) (pcode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenProvableV TAct k (guardCodeB (tcode phiG) (pcode (GuardianBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (GuardianBot k)) (pcode (PrudentBot k)) (pcode (GuardianBot k)) (actCode .C) ∧
        (¬ LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (GuardianBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (GuardianBot k)) (pcode (PrudentBot k)) (actCode .D)) ∧
        (LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (GuardianBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (GuardianBot k)) (pcode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_GuardianBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_GuardianBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hG, hn⟩ := h₁ k (by omega)
  refine ⟨hG, fun h ↦ ?_⟩
  obtain ⟨hGC, hPD, hPC⟩ := hn h
  exact ⟨hGC, fun hA ↦ hPD (Or.inl hA), fun hA ↦ hPC hA (by rw [hingeB]; exact hB k (by omega))⟩

/-- **Wary × Prudent** (engine `llm_outcome_WaryBot_vs_PrudentBot = (C, D)`, pad 3), the prudence hinge discharged:
two hinges, NESTED — Prudent's outer guard `A` "Wary plays C against me" (outer split), then `W` = Wary's `.neg` guard
"¬(Prudent plays C against me)". `A ⇒ (C, C)`; `¬A ⇒` Prudent D, `W ⇒` Wary D, `¬W ⇒` Wary C (the engine's world). -/
theorem dich_WaryBot_vs_PrudentBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (WaryBot k)) k) →
        EvalGraph 3 (pcode (WaryBot k)) (pcode (PrudentBot k)) (pcode (WaryBot k)) (actCode .C) ∧
        EvalGraph 3 (pcode (PrudentBot k)) (pcode (WaryBot k)) (pcode (PrudentBot k)) (actCode .C)) ∧
      (¬ LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (WaryBot k)) k) →
        EvalGraph 3 (pcode (PrudentBot k)) (pcode (WaryBot k)) (pcode (PrudentBot k)) (actCode .D) ∧
        (LenProvableV TAct k (guardCodeB (tcode phiW) (pcode (WaryBot k)) (pcode (PrudentBot k)) k) →
          EvalGraph 3 (pcode (WaryBot k)) (pcode (PrudentBot k)) (pcode (WaryBot k)) (actCode .D)) ∧
        (¬ LenProvableV TAct k (guardCodeB (tcode phiW) (pcode (WaryBot k)) (pcode (PrudentBot k)) k) →
          EvalGraph 3 (pcode (WaryBot k)) (pcode (PrudentBot k)) (pcode (WaryBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_WaryBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_WaryBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hAB, hn⟩ := h₁ k (by omega)
  exact ⟨fun hA ↦ hAB hA (by rw [hingeB]; exact hB k (by omega)), fun hA ↦ hn (Or.inl hA)⟩

/-- **Cupod × Prudent** (engine `outcome_CupodBot_vs_PrudentBot = (C, D)`, pad 3), the prudence hinge discharged:
two hinges, NESTED — `Cu` = Cupod's guard "Prudent plays D against me" (outer split), then Prudent's outer guard `A`
"Cupod plays C against me". `Cu ⇒ (D, D)`; `¬Cu ⇒` Cupod C, `¬A ⇒` Prudent D (the engine's world), `A ⇒` Prudent C. -/
theorem dich_CupodBot_vs_PrudentBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenProvableV TAct k (guardCodeB (tcode phiCu) (pcode (CupodBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (CupodBot k)) (pcode (PrudentBot k)) (pcode (CupodBot k)) (actCode .D) ∧
        EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .D)) ∧
      (¬ LenProvableV TAct k (guardCodeB (tcode phiCu) (pcode (CupodBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (CupodBot k)) (pcode (PrudentBot k)) (pcode (CupodBot k)) (actCode .C) ∧
        (¬ LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (CupodBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .D)) ∧
        (LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (CupodBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₁, h₁⟩ := dich_CupodBot_vs_PrudentBot
  obtain ⟨k₂, hB⟩ := prudence_found_vs_CupodBot
  refine ⟨k₁ + k₂, fun k hk ↦ ?_⟩
  obtain ⟨hCu, hn⟩ := h₁ k (by omega)
  refine ⟨hCu, fun h ↦ ?_⟩
  obtain ⟨hCC, hPD, hPC⟩ := hn h
  exact ⟨hCC, fun hA ↦ hPD (Or.inl hA), fun hA ↦ hPC hA (by rw [hingeB]; exact hB k (by omega))⟩

/-- **Prudent × Cupod** (engine `outcome_PrudentBot_vs_CupodBot = (D, C)`, pad 3): the same pair, Prudent's side first,
the prudence hinge discharged. -/
theorem dich_PrudentBot_vs_CupodBot_prudenceFound :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (LenProvableV TAct k (guardCodeB (tcode phiCu) (pcode (CupodBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .D) ∧
        EvalGraph 3 (pcode (CupodBot k)) (pcode (PrudentBot k)) (pcode (CupodBot k)) (actCode .D)) ∧
      (¬ LenProvableV TAct k (guardCodeB (tcode phiCu) (pcode (CupodBot k)) (pcode (PrudentBot k)) k) →
        EvalGraph 3 (pcode (CupodBot k)) (pcode (PrudentBot k)) (pcode (CupodBot k)) (actCode .C) ∧
        (¬ LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (CupodBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .D)) ∧
        (LenProvableV TAct k (guardCodeB (tcode phiPo) (pcode (PrudentBot k)) (pcode (CupodBot k)) k) →
          EvalGraph 3 (pcode (PrudentBot k)) (pcode (CupodBot k)) (pcode (PrudentBot k)) (actCode .C))) := by
  obtain ⟨k₀, h⟩ := dich_CupodBot_vs_PrudentBot_prudenceFound
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨h1, h2⟩ := h k hk
  exact ⟨fun hCu ↦ ⟨(h1 hCu).2, (h1 hCu).1⟩, h2⟩

end restated

end ArithS

import ArithS.Cells.PositiveCells
import ArithS.Cells.DIMCID

/-!
# ArithS.Cells.DupocEngine — Dupoc's Löb cells on the ENGINE's `DupocBot`/`CupodBot`

The four Löb cells of Dupoc and Cupod that `Cells/DupocMirror.lean` (`loeb_Dupoc_vs_Mirror`,
`loeb_Cupod_vs_Mirror`) and `Necessitation/Package.lean` (`dupoc_self_coop`) prove on the hand-template
twins `Dupoc k`/`Cupod k` (template `guardTemplate`), re-proved here on the engine's own codes
`progCode (DupocBot k) = SV gDu 0 k` and `progCode (CupodBot k) = SV gCu 1 k` (template
`template (.plays .opp .self .C)` and its transposition, `progCode_DupocBot_SV`/`progCode_CupodBot_SV`).
This retires the twin-named cells `outcome_Dupoc_vs_Dupoc`, `outcome_Dupoc_vs_MirrorBot`,
`outcome_Cupod_vs_Cupod`, `outcome_Cupod_vs_MirrorBot` of `Outcome/Matrix/` in favour of
`outcome_DupocBot_vs_DupocBot`, `outcome_DupocBot_vs_MirrorBot`, `outcome_CupodBot_vs_CupodBot`,
`outcome_CupodBot_vs_MirrorBot`. The hand-twin theorems themselves are untouched.

The pattern is `Cells/FlipCells.lean` §6 (Wary × Wary, Wary × Mirror) with Dupoc's positive guard in
place of Wary's `.neg` guard:

1. **Self-play.** The fixed formula `qDuDu := qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (TS gDu 0) (uS gDu 0) (wS gDu 0)`
   — "the program the opp-triple describes plays C against the one the me-triple describes", both triples
   Dupoc's `SV` description — with the instance equations `guardCode_DuDu` (Dupoc's guard against itself
   is the `binNumeral k`-instance of `⌜qDuDu⌝`) and `guardCode_DuDuT` (Cupod's, of the transposition),
   the truth equations `eval_qDuDu_iff`/`eval_qDuDuT_iff`, and the Löb premise `loebSound_pDuDu`
   for the two-guard family `pQ qDuDu = qDuDu ⋏ τ qDuDu` (`loebSound_pQ_of`): both boxes make both
   searchers find their guards (`SV_search_V`), so Dupoc cooperates with Dupoc and Cupod defects against
   Cupod, which is what the two conjuncts say. Then `family_found` at `boundedInnerNec_sixteen`:
   **`loeb_DupocBot_vs_DupocBot`** `(C, C)` and **`loeb_CupodBot_vs_CupodBot`** `(D, D)`, with the box
   forms `_guard`.
2. **Against Mirror.** The same with Mirror's closed triple `(cl TM, numT 0, numT 1)` in the opp-slots
   (`qDuM`, `guardCode_DuM`/`guardCode_DuMT`, `eval_qDuM_iff`/`eval_qDuMT_iff`, `loebSound_pDuM`: Mirror
   COPIES at fuel 3, `mirror_copies2_V`): **`loeb_DupocBot_vs_MirrorBot`** `(C, C)` and
   **`loeb_CupodBot_vs_MirrorBot`** `(D, D)`, with the box forms `_guard`.

Every threshold is EXISTENTIAL; `simp` never sees a closed quote; `omega` is never asked about `V`;
`≤` at ℕ is bridged by `le_def`; `V` is pinned in every statement.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The transposed Dupoc triple describes the engine's Cupod -/

section triples

/-- The transposed Dupoc triple describes the transposed searcher `SV gCu 1 k` — the engine's `CupodBot k`
(values). -/
lemma desc_DuT (k : V) :
    revalue ((Semiterm.lMap swap (uS gDu 0)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS gDu 0)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS gDu 0)).val (s := stdReadingV V) ![k] Empty.elim) = SV gCu 1 k := by
  have := descT_SV gDu 0 (Or.inl rfl) k
  rwa [lMap_swap_gDu] at this

end triples

/-! ### 2. Self-play: DupocBot × DupocBot `(C, C)`, CupodBot × CupodBot `(D, D)` -/

section selfPlay

/-- Dupoc's guard against itself: "`DupocBot k` plays C against `DupocBot k`" (both triples Dupoc's). -/
noncomputable def qDuDu : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (TS gDu 0) (uS gDu 0) (wS gDu 0)

lemma qDuDu_swap :
    Semiformula.lMap swap qDuDu =
      qT gCu (Semiterm.lMap swap (TS gDu 0)) (Semiterm.lMap swap (uS gDu 0)) (Semiterm.lMap swap (wS gDu 0))
        (Semiterm.lMap swap (TS gDu 0)) (Semiterm.lMap swap (uS gDu 0)) (Semiterm.lMap swap (wS gDu 0)) := by
  unfold qDuDu
  rw [lMap_swap_qT, lMap_swap_gDu]

/-- **The instance equation on codes**: Dupoc's guard code against itself is the `binNumeral k`-instance of
`⌜qDuDu⌝`, in every model. -/
theorem guardCode_DuDu (k : V) : guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (SV gDu 0 k) = instB (⌜qDuDu⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k)

/-- The transposed instance equation: Cupod's guard code against itself is the instance of `τ qDuDu`. -/
theorem guardCode_DuDuT (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (SV gCu 1 k) = instB (⌜Semiformula.lMap swap qDuDu⌝ : V) k := by
  have := guardCode_qT_swap_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k)
  rwa [transposeCode_SV gDu 0 (Or.inl rfl), lMap_swap_gDu] at this

/-- `qDuDu(k)` in the standard reading: `DupocBot k` plays C against `DupocBot k`. -/
theorem eval_qDuDu_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qDuDu ↔
      ∃ n, EvalGraph n (SV gDu 0 k) (SV gDu 0 k) (SV gDu 0 k) 0 := by
  rw [qDuDu, eval_qT_plays_opp_self .C _ _ _ _ _ _ k (desc_SV gDu 0 (Or.inl rfl) k) (desc_SV gDu 0 (Or.inl rfl) k),
    actCode_C_cast]

/-- `τ qDuDu (k)` in the standard reading: `CupodBot k` plays D against `CupodBot k`. -/
theorem eval_qDuDuT_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qDuDu) ↔
      ∃ n, EvalGraph n (SV gCu 1 k) (SV gCu 1 k) (SV gCu 1 k) 1 := by
  rw [qDuDu_swap, eval_qT_plays_opp_self .D _ _ _ _ _ _ k (desc_DuT k) (desc_DuT k), actCode_D_cast]

/-- **Dupoc's Löb premise in self-play, slack `(7, 8)`**: a box of the family makes Dupoc FIND its guard, so
Dupoc cooperates with itself (fuel 2) — the guard "Dupoc plays C against me" is TRUE; the transposed searcher
likewise defects against itself. Both readings. -/
theorem loebSound_pDuDu : LoebSound (pQ qDuDu) 7 8 := by
  refine loebSound_pQ_of qDuDu fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_DuDu] at h1
  rw [← guardCode_DuDuT] at h2
  have e1 := SV_search_V gDu 0 k (SV gDu 0 k) h1
  have e2 := SV_search_V gCu 1 k (SV gCu 1 k) h2
  rw [Nat.cast_zero] at e1
  rw [Nat.cast_one] at e2
  rw [← stdReadingV_eq_stdReading, eval_qDuDu_iff, eval_qDuDuT_iff]
  exact ⟨⟨2, e1⟩, ⟨2, e2⟩⟩

/-- **The self-play cells, packaged**: for all large `k`, the engine's `DupocBot k` cooperates with itself and
`CupodBot k` defects against itself (fuel 2), and both FIND their guards within the budget — `family_found`
on `pQ qDuDu` (the arithmetized `pblt_engine`), then ∧-elimination on codes. -/
theorem loeb_DupocBot_self_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (progCode (DupocBot k)) (progCode (DupocBot k)) (progCode (DupocBot k)) 0 ∧
        EvalGraph 2 (progCode (CupodBot k)) (progCode (CupodBot k)) (progCode (CupodBot k)) 1) ∧
      (LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (DupocBot k))) ∧
        LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (CupodBot k)))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qDuDu) boundedInnerNec_sixteen loebSound_pDuDu
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qDuDu k) ha)
  obtain ⟨h1, h2⟩ := pQ_both_V (V := ℕ) qDuDu k a ha' hpc
  rw [← guardCode_DuDu] at h1
  rw [← guardCode_DuDuT] at h2
  rw [progCode_DupocBot_SV, progCode_CupodBot_SV]
  exact ⟨⟨SV_search_V (V := ℕ) gDu 0 k (SV gDu 0 k) h1, SV_search_V (V := ℕ) gCu 1 k (SV gCu 1 k) h2⟩, h1, h2⟩

/-- **DupocBot × DupocBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own
code (Critch's Theorem 3.7; the hand-twin form is `dupoc_self_coop`): `DupocBot k` cooperates with itself. -/
theorem loeb_DupocBot_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocBot k)) (progCode (DupocBot k)) (progCode (DupocBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_self_core
  exact ⟨k₀, fun k hk ↦ (h k hk).1.1⟩

/-- **CupodBot × CupodBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own
code (the τ half of `loeb_DupocBot_vs_DupocBot`): `CupodBot k` defects against itself. -/
theorem loeb_CupodBot_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CupodBot k)) (progCode (CupodBot k)) (progCode (CupodBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_self_core
  exact ⟨k₀, fun k hk ↦ (h k hk).1.2⟩

/-- **The box form**: Dupoc FINDS its guard against itself within its budget, for all large `k`. -/
theorem loeb_DupocBot_vs_DupocBot_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (DupocBot k))) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_self_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **The box form**: Cupod FINDS its guard against itself within its budget, for all large `k`. -/
theorem loeb_CupodBot_vs_CupodBot_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (CupodBot k))) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_self_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2.2⟩

end selfPlay

/-! ### 3. Against Mirror: DupocBot × MirrorBot `(C, C)`, CupodBot × MirrorBot `(D, D)` -/

section mirror

/-- Dupoc's guard against Mirror: "Mirror plays C against `DupocBot k`" (Mirror's closed triple in the
opp-slots). -/
noncomputable def qDuM : Semisentence LAct 1 :=
  qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) (cl TM) (numT 0) (numT 1)

lemma qDuM_swap :
    Semiformula.lMap swap qDuM =
      qT gCu (Semiterm.lMap swap (TS gDu 0)) (Semiterm.lMap swap (uS gDu 0)) (Semiterm.lMap swap (wS gDu 0))
        (cl TM) (numT 0) (numT 1) := by
  unfold qDuM
  rw [lMap_swap_qT, lMap_swap_gDu, lMap_swap_cl, lMap_swap_TM, lMap_swap_numT, lMap_swap_numT]

/-- **The instance equation on codes**: Dupoc's guard code against Mirror is the `binNumeral k`-instance of
`⌜qDuM⌝`, in every model. -/
theorem guardCode_DuM (k : V) : guardCode (⌜gDu⌝ : V) (SV gDu 0 k) MirrorV = instB (⌜qDuM⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_mirror k) hU_mirror hW_mirror

/-- The transposed instance equation: Cupod's guard code against Mirror (τ-fixed) is the instance of `τ qDuM`. -/
theorem guardCode_DuMT (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) MirrorV = instB (⌜Semiformula.lMap swap qDuM⌝ : V) k := by
  have := guardCode_qT_swap_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_mirror k) hU_mirror hW_mirror
  rwa [transposeCode_SV gDu 0 (Or.inl rfl), lMap_swap_gDu, transposeCode_MirrorV] at this

/-- `qDuM(k)` in the standard reading: Mirror plays C against `DupocBot k`. -/
theorem eval_qDuM_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qDuM ↔
      ∃ n, EvalGraph n MirrorV (SV gDu 0 k) MirrorV 0 := by
  rw [qDuM, eval_qT_plays_opp_self .C _ _ _ _ _ _ k (desc_SV gDu 0 (Or.inl rfl) k) (desc_mirror k), actCode_C_cast]

/-- `τ qDuM (k)` in the standard reading: Mirror plays D against `CupodBot k`. -/
theorem eval_qDuMT_iff (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qDuM) ↔
      ∃ n, EvalGraph n MirrorV (SV gCu 1 k) MirrorV 1 := by
  rw [qDuM_swap, eval_qT_plays_opp_self .D _ _ _ _ _ _ k (desc_DuT k) (desc_mirror k), actCode_D_cast]

/-- **Dupoc's Löb premise against Mirror, slack `(7, 8)`**: a box of the family makes Dupoc FIND its guard, so
Dupoc cooperates (fuel 2), so Mirror copies (fuel 3) — the guard "Mirror plays C against me" is TRUE; the
transposed searcher defects and Mirror copies that. Both readings. -/
theorem loebSound_pDuM : LoebSound (pQ qDuM) 7 8 := by
  refine loebSound_pQ_of qDuM fun V _ _ k h1 h2 ↦ ?_
  rw [← guardCode_DuM] at h1
  rw [← guardCode_DuMT] at h2
  have e1 := mirror_copies2_V _ _ (SV_search_V gDu 0 k MirrorV h1)
  have e2 := mirror_copies2_V _ _ (SV_search_V gCu 1 k MirrorV h2)
  rw [Nat.cast_zero] at e1
  rw [Nat.cast_one] at e2
  rw [← stdReadingV_eq_stdReading, eval_qDuM_iff, eval_qDuMT_iff]
  exact ⟨⟨3, e1⟩, ⟨3, e2⟩⟩

/-- **The Mirror cells, packaged**: for all large `k`, the engine's `DupocBot k` cooperates with Mirror and
`CupodBot k` defects against Mirror (fuel 2), and both FIND their guards within the budget. -/
theorem loeb_DupocBot_mirror_core :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (progCode (DupocBot k)) (progCode MirrorBot) (progCode (DupocBot k)) 0 ∧
        EvalGraph 2 (progCode (CupodBot k)) (progCode MirrorBot) (progCode (CupodBot k)) 1) ∧
      (LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode MirrorBot)) ∧
        LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode MirrorBot))) := by
  obtain ⟨k₀, hf⟩ := family_found (pQ qDuM) boundedInnerNec_sixteen loebSound_pDuM
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := hf k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pQ (V := ℕ) qDuM k) ha)
  obtain ⟨h1, h2⟩ := pQ_both_V (V := ℕ) qDuM k a ha' hpc
  rw [← guardCode_DuM] at h1
  rw [← guardCode_DuMT] at h2
  rw [progCode_DupocBot_SV, progCode_CupodBot_SV, progCode_MirrorBot, ← MirrorV_nat]
  exact ⟨⟨SV_search_V (V := ℕ) gDu 0 k MirrorV h1, SV_search_V (V := ℕ) gCu 1 k MirrorV h2⟩, h1, h2⟩

/-- **DupocBot × MirrorBot is `(C, C)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own
code (the hand-twin form is `loeb_Dupoc_vs_Mirror`): `DupocBot k` cooperates with Mirror (fuel 2) and Mirror
copies (fuel 3). -/
theorem loeb_DupocBot_vs_MirrorBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DupocBot k)) (progCode MirrorBot) (progCode (DupocBot k)) (actCode .C) ∧
      EvalGraph 3 (progCode MirrorBot) (progCode (DupocBot k)) (progCode MirrorBot) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_mirror_core
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies (h k hk).1.1⟩⟩

/-- **CupodBot × MirrorBot is `(D, D)` in PA-`S'`**, for all large `k`, unconditional, on the engine's own
code (the hand-twin form is `loeb_Cupod_vs_Mirror`): `CupodBot k` defects against Mirror (fuel 2) and Mirror
copies (fuel 3). -/
theorem loeb_CupodBot_vs_MirrorBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CupodBot k)) (progCode MirrorBot) (progCode (CupodBot k)) (actCode .D) ∧
      EvalGraph 3 (progCode MirrorBot) (progCode (CupodBot k)) (progCode MirrorBot) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_mirror_core
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.2, mirror_copies (h k hk).1.2⟩⟩

/-- **The box form**: Dupoc FINDS its guard against Mirror within its budget, for all large `k`. -/
theorem loeb_DupocBot_vs_MirrorBot_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode MirrorBot)) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_mirror_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **The box form**: Cupod FINDS its guard against Mirror within its budget, for all large `k`. -/
theorem loeb_CupodBot_vs_MirrorBot_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode MirrorBot)) := by
  obtain ⟨k₀, h⟩ := loeb_DupocBot_mirror_core
  exact ⟨k₀, fun k hk ↦ (h k hk).2.2⟩

end mirror

end ArithS

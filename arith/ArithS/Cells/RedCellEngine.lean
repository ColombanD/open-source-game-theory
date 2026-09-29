import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Cells.RedCellEngine — the red cell on the ENGINE's `DupocBot`/`CupodBot`

`Cells/RedCell.lean` proves `(Dupoc, Cupod) = (D, C)` for the hand-written searchers `Dupoc k`/
`Cupod k` (template `guardTemplate`). The engine's `DupocBot k` is a different code — its guard is the
translated template `tmpl (.plays .opp .self .C)` — with the same argument available through the
general machinery: `swapcode_pcode` + `lMap_swap_trAt_plays` (τ-symmetry of the two guards),
`play_of_found_opp_self` (soundness: a found guard is a true play), `EvalGraph.unique'`
(determinism). No Löb, no census, every budget `k`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus
open LAct
open PD.Bots

theorem fragP_CupodBot (k : ℕ) : fragP (CupodBot k) = true := rfl

lemma transpose_DupocBot (k : ℕ) : (DupocBot k).transpose = CupodBot k := rfl
lemma transpose_CupodBot (k : ℕ) : (CupodBot k).transpose = DupocBot k := rfl

/-- **Symmetry of the guards** (engine codes): Dupoc's guard against Cupod is found within `k`
iff Cupod's guard against Dupoc is. -/
theorem guard_DupocBot_iff_guard_CupodBot (k : ℕ) :
    LenProvableV TAct k (guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode (CupodBot k))) ↔
    LenProvableV TAct k (guardCode (tcode phiCu) (pcode (CupodBot k)) (pcode (DupocBot k))) := by
  rw [← quote_trAt, ← quote_trAt, lenProvableV_nat, lenProvableV_nat, lenProvable_fbound_swap_iff]
  unfold phiDu phiCu
  rw [lMap_swap_trAt_plays (fragP_DupocBot k) (fragP_CupodBot k) rfl rfl, transpose_DupocBot,
    transpose_CupodBot]
  rfl

/-- **The red cell on the engine's bots**: `DupocBot k` defects against `CupodBot k` and
`CupodBot k` cooperates with `DupocBot k`, at every shared budget `k`. -/
theorem snd_DupocBot_vs_CupodBot (k : ℕ) :
    EvalGraph 2 (pcode (DupocBot k)) (pcode (CupodBot k)) (pcode (DupocBot k)) (actCode .D) ∧
    EvalGraph 2 (pcode (CupodBot k)) (pcode (DupocBot k)) (pcode (CupodBot k)) (actCode .C) := by
  have hG : ¬ LenProvableV TAct k (guardCode (tcode phiDu) (pcode (DupocBot k)) (pcode (CupodBot k))) := by
    intro hD
    have hC := (guard_DupocBot_iff_guard_CupodBot k).mp hD
    -- Cupod's guard is true: Dupoc defects against Cupod.
    obtain ⟨N, hN⟩ := play_of_found_opp_self (proper_CupodBot k) (proper_DupocBot k) .D hC
    -- But Dupoc, finding its proof, cooperates.
    have hcoop : EvalGraph 2 (pcode (DupocBot k)) (pcode (CupodBot k)) (pcode (DupocBot k)) (actCode .C) := by
      rw [pcode_DupocBot_search]
      show EvalGraph (1 + 1) _ _ (pSearch k (tcode phiDu) (pConst 0) (pConst 1)) _
      rw [EvalGraph.search_iff₆ (isSemiformula_tcode _)]
      rw [pcode_DupocBot_search] at hD
      exact Or.inl ⟨hD, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    exact absurd (EvalGraph.unique' hN hcoop) (by decide)
  have hG' : ¬ LenProvableV TAct k (guardCode (tcode phiCu) (pcode (CupodBot k)) (pcode (DupocBot k))) :=
    fun h ↦ hG ((guard_DupocBot_iff_guard_CupodBot k).mpr h)
  constructor
  · rw [pcode_DupocBot_search]
    show EvalGraph (1 + 1) _ _ (pSearch k (tcode phiDu) (pConst 0) (pConst 1)) _
    rw [EvalGraph.search_iff₆ (isSemiformula_tcode _)]
    rw [pcode_DupocBot_search] at hG
    exact Or.inr ⟨hG, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
  · rw [pcode_CupodBot]
    show EvalGraph (1 + 1) _ _ (pSearch k (tcode phiCu) (pConst 1) (pConst 0)) _
    rw [EvalGraph.search_iff₆ (isSemiformula_tcode _)]
    rw [pcode_CupodBot] at hG'
    exact Or.inr ⟨hG', (EvalGraph.const_iff (n := 0)).mpr rfl⟩

end ArithS

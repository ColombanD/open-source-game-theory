import ArithS.Cells.FloorDichotomy

/-!
# ArithS.Cells.RedCellEngine — the red cell on the ENGINE's `DupocBot`/`CupodBot`

`Cells/RedCell.lean` proves `(Dupoc, Cupod) = (D, C)` for the hand-written searchers `Dupoc k`/
`Cupod k` (template `guardTemplate`). The engine's `DupocBot k` is a different code — its guard is the
translated template `template (.plays .opp .self .C)` — with the same argument available through the
general machinery: `transposeCode_progCode` + `lMap_swap_sentenceAt_plays` (τ-symmetry of the two guards),
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
    LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodBot k))) ↔
    LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (DupocBot k))) := by
  rw [← quote_sentenceAt, ← quote_sentenceAt, lenBox_nat, lenBox_nat, lenBoxNat_swap_iff]
  unfold phiDu phiCu
  rw [lMap_swap_sentenceAt_plays (fragP_DupocBot k) (fragP_CupodBot k) rfl rfl, transpose_DupocBot,
    transpose_CupodBot]
  rfl

/-- **The red cell on the engine's bots**: `DupocBot k` defects against `CupodBot k` and
`CupodBot k` cooperates with `DupocBot k`, at every shared budget `k`. -/
theorem snd_DupocBot_vs_CupodBot (k : ℕ) :
    EvalGraph 2 (progCode (DupocBot k)) (progCode (CupodBot k)) (progCode (DupocBot k)) (actCode .D) ∧
    EvalGraph 2 (progCode (CupodBot k)) (progCode (DupocBot k)) (progCode (CupodBot k)) (actCode .C) := by
  have hG : ¬ LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodBot k))) := by
    intro hD
    have hC := (guard_DupocBot_iff_guard_CupodBot k).mp hD
    -- Cupod's guard is true: Dupoc defects against Cupod.
    obtain ⟨N, hN⟩ := play_of_found_opp_self (properPlayer_CupodBot k) (properPlayer_DupocBot k) .D hC
    -- But Dupoc, finding its proof, cooperates.
    have hcoop : EvalGraph 2 (progCode (DupocBot k)) (progCode (CupodBot k)) (progCode (DupocBot k)) (actCode .C) := by
      rw [progCode_DupocBot_search]
      show EvalGraph (1 + 1) _ _ (pSearch k (templateCode phiDu) (pConst 0) (pConst 1)) _
      rw [EvalGraph.search_iff₆ (isSemiformula_templateCode _)]
      rw [progCode_DupocBot_search] at hD
      exact Or.inl ⟨hD, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
    exact absurd (EvalGraph.unique' hN hcoop) (by decide)
  have hG' : ¬ LenBox TAct k (guardCode (templateCode phiCu) (progCode (CupodBot k)) (progCode (DupocBot k))) :=
    fun h ↦ hG ((guard_DupocBot_iff_guard_CupodBot k).mpr h)
  constructor
  · rw [progCode_DupocBot_search]
    show EvalGraph (1 + 1) _ _ (pSearch k (templateCode phiDu) (pConst 0) (pConst 1)) _
    rw [EvalGraph.search_iff₆ (isSemiformula_templateCode _)]
    rw [progCode_DupocBot_search] at hG
    exact Or.inr ⟨hG, (EvalGraph.const_iff (n := 0)).mpr rfl⟩
  · rw [progCode_CupodBot]
    show EvalGraph (1 + 1) _ _ (pSearch k (templateCode phiCu) (pConst 1) (pConst 0)) _
    rw [EvalGraph.search_iff₆ (isSemiformula_templateCode _)]
    rw [progCode_CupodBot] at hG'
    exact Or.inr ⟨hG', (EvalGraph.const_iff (n := 0)).mpr rfl⟩

end ArithS

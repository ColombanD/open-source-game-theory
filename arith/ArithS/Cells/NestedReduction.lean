import ArithS.Cells.ConReduction
import ArithS.Cells.SelfDual
import ArithS.Cells.TrollReduction

/-!
# ArithS.Cells.NestedReduction — the nested floor `CIMCIC × Cupod` (= `DIMDID × Dupoc`): every hinge reduces

`Cells/ConReduction` reduces the OUTER hinge of `CIMCIC × CupodBot` (CIMCIC's guard) to literal bounded
consistency. This module adds the INNER one — Cupod's guard "CIMCIC plays D against me": true in a model, it means
CIMCIC did not play its then-branch, i.e. CIMCIC's own guard was NOT found there — and carries both across the
transposition to `DIMDID × DupocBot` (`Cells/SelfDual.guards_DIMDID_DupocBot_iff_CIMCIC_CupodBot`: the two pairs
are one floor, their hinges coincide pairwise).

So for each of the four hinges `H` of the two pairs: for all large `k`, `H` found within `k` yields a `TAct`-proof,
within `k + D₀ + D₁·size k + D₂·(size k)²`, that `⊥` has no proof within `k − C₀ − C₁·size k`. One direction only,
as everywhere in `ConReduction`; the pair is NOT decided (three outcomes remain consistent: neither hinge, the
outer one, the inner one — never both, by soundness).
§3 adds the LITERAL form for `Dupoc × CupodTroll` (`Cells/TrollReduction` states its two-way reduction on the
troll's `.eq` guard): with it, every hinge of the nine floors of the 12-bot ladder yields `Con_TAct` below `k`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

/-! ### 1. Cupod's hinge against CIMCIC -/

/-- Cupod's hinge against CIMCIC, as a fixed formula: "CIMCIC plays D against `CupodBot k`". -/
noncomputable def rCuCi : Semisentence LAct 1 := qF (gP .D) dpCu dpCi

/-- Cupod's hinge against CIMCIC, as consulted by the evaluator, is the `binNumeral k`-instance of `rCuCi`. -/
theorem hinge_CupodBot_vs_CIMCIC_eq (k : ℕ) :
    guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)) k =
      (⌜(rCuCi ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  have h1 : dpCu.val (V := ℕ) k = progCode (CupodBot k) := by rw [dpCu_val, progCode_CupodBot_SV]; rfl
  have h2 : dpCi.val (V := ℕ) k = progCode (CIMCIC k) := by rw [dpCi_val, progCode_CIMCIC_SV]; rfl
  rw [hingeB phiCu, templateCode_eq_quote_template phiCu rfl, ← h1, ← h2]
  have e := guardCode_qF (V := ℕ) (gP .D) dpCu dpCi k
  have hq : instB (⌜rCuCi⌝ : ℕ) k =
      ⌜(rCuCi ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ := by
    have := quote_instB (V := ℕ) rCuCi k
    rwa [natCast_nat] at this
  rw [← hq]
  exact e

/-- **THE REDUCTION, the INNER hinge of CIMCIC × CupodBot**: Cupod's guard "CIMCIC plays D against me", when true,
means CIMCIC's guard against Cupod was not found. -/
theorem hinge_reduces_to_bounded_consistency_CupodBot_vs_CIMCIC :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiCu) (progCode (CupodBot k)) (progCode (CIMCIC k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  refine hinge_con_reduction rCuCi [rCi dpCu, Semiformula.lMap swap (rCi dpCu)] 0
    (fun M _ _ x _ hr ↦ ?_) (fun M _ _ x _ hr ↦ ?_) _ hinge_CupodBot_vs_CIMCIC_eq
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    refine ⟨rCi dpCu, by simp, ?_⟩
    obtain ⟨n, hn⟩ := (eval_qF_plays .D dpCu dpCi x).mp hr
    rw [dpCi_val] at hn
    unfold rCi
    rw [← guardCode_qF, dpCi_val]
    exact not_found_of_SV_play hn (by simp [actCode])
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    refine ⟨Semiformula.lMap swap (rCi dpCu), by simp, ?_⟩
    unfold rCuCi at hr
    rw [eval_swappedReading, lMap_swap_qF, lMap_swap_gP_D, ← stdReadingV_eq_stdReading] at hr
    obtain ⟨n, hn⟩ := (eval_qF_plays .C dpCu.tr dpCi.tr x).mp hr
    rw [dpCi_tr_val] at hn
    rw [lMap_swap_rCi, ← guardCode_qF, dpCi_tr_val]
    exact not_found_of_SV_play hn (by simp [actCode])

/-! ### 2. Across the transposition: `DIMDID × DupocBot` -/

/-- **THE REDUCTION, the OUTER hinge of DIMDID × DupocBot** (DIMDID's guard): the τ-image of CIMCIC's guard against
Cupod, found at the same budgets. -/
theorem hinge_reduces_to_bounded_consistency_DIMDID_vs_DupocBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiDd) (progCode (DIMDID k)) (progCode (DupocBot k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨k₀, C₀, C₁, D₀, D₁, D₂, h⟩ := hinge_reduces_to_bounded_consistency_CIMCIC_vs_CupodBot
  refine ⟨k₀, C₀, C₁, D₀, D₁, D₂, fun k hk hA ↦ h k hk ?_⟩
  rw [hingeB phiDd] at hA
  rw [hingeB phiC]
  exact (guards_DIMDID_DupocBot_iff_CIMCIC_CupodBot k).1.mp hA

/-- **THE REDUCTION, the INNER hinge of DIMDID × DupocBot** (Dupoc's guard "DIMDID cooperates with me"): the
τ-image of Cupod's guard against CIMCIC. -/
theorem hinge_reduces_to_bounded_consistency_DupocBot_vs_DIMDID :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (DIMDID k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  obtain ⟨k₀, C₀, C₁, D₀, D₁, D₂, h⟩ := hinge_reduces_to_bounded_consistency_CupodBot_vs_CIMCIC
  refine ⟨k₀, C₀, C₁, D₀, D₁, D₂, fun k hk hB ↦ h k hk ?_⟩
  rw [hingeB phiDu] at hB
  rw [hingeB phiCu]
  exact (guards_DIMDID_DupocBot_iff_CIMCIC_CupodBot k).2.mp hB

/-! ### 3. Dupoc × CupodTroll, literal form -/

section trollLiteral

open ArithS.Tau

/-- **Dupoc × CupodTroll, literal form**: the hinge within `k` ⇒ `Con_TAct(k − C₀ − C₁·size k)` within
`k + D₀ + D₁·size k + D₂·(size k)²` (compare `hinge_reduces_to_bounded_consistency_DupocBot_vs_CupodTrollBot`, on
the troll's `.eq` guard `ε_k`): the troll's C against Dupoc is its else-branch, so `ε_k` (standard reading) or its
τ-twin (swapped reading) was not found — which a short proof of `⊥` forbids. -/
theorem hinge_reduces_to_literal_consistency_DupocBot_vs_CupodTrollBot :
    ∃ k₀ C₀ C₁ D₀ D₁ D₂ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCodeB (templateCode phiDu) (progCode (DupocBot k)) (progCode (CupodTrollBot k)) k) →
      LenBox TAct (k + D₀ + D₁ * Nat.size k + D₂ * Nat.size k * Nat.size k)
        (⌜(conBelow C₀ C₁ ⇜ ![Semiterm.lMap emb (binNumeralMeta k)] : Sentence LAct)⌝ : ℕ) := by
  refine hinge_con_reduction rTr [qEps, Semiformula.lMap swap qEps] 0
    (fun M _ _ x _ hr ↦ ?_) (fun M _ _ x _ hr ↦ ?_) _ hinge_DupocBot_vs_CupodTrollBot_eq
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    refine ⟨qEps, by simp, ?_⟩
    obtain ⟨n, hn⟩ := (eval_qF_plays .C dpDu dpT x).mp hr
    rw [qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_D M), dpT_val]
    rw [dpT_val] at hn
    refine sm_not_found_of_play_V (sTc .D) hn ?_
    show ((actCode .C : ℕ) : M) ≠ ((actCode .D : ℕ) : M)
    rw [actCode_C_cast, actCode_D_cast]
    exact _root_.zero_ne_one
  · have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
    refine ⟨Semiformula.lMap swap qEps, by simp, ?_⟩
    rw [eval_swappedReading, ← stdReadingV_eq_stdReading, rTr, lMap_swap_qF, lMap_swap_gP_C] at hr
    obtain ⟨n, hn⟩ := (eval_qF_plays .D dpDu.tr dpT.tr x).mp hr
    rw [lMap_swap_qEps, ← guardCodeB_qF13 _ (isSemiformula7_gEq_C M), dpT_tr_val]
    rw [dpT_tr_val] at hn
    refine sm_not_found_of_play_V (sTc .C) hn ?_
    show ((actCode .D : ℕ) : M) ≠ ((actCode .C : ℕ) : M)
    rw [actCode_C_cast, actCode_D_cast]
    exact _root_.one_ne_zero

end trollLiteral

end ArithS

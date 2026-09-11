import ArithS.Transparency
import ArithS.Diag
import ArithS.ProperV

/-!
# ArithS.Assembly.Prep — every lemma the PBLT assembly (U8) needs that is not yet in the package

M4 items of `Research/Notes/M4_BOUNDED_HBL/BRIEF.md` §6–§7 (with the §7 addendum: the Löb
family is the CONJUNCTION `qDupoc ⋏ qCupod`). V-generic (every model of `𝗜𝚺₁`, budgets `k : V`
possibly nonstandard) unless a statement says `ℕ`.

1. **Cupod's instance.** `CupodV k = swapcode (DupocV k)` (`ArithS.InstanceV`), the one-variable
   formula `qCupod := lMap swap qDupoc`, and the instance equation on codes
   `guardCode_CupodV_eq_instB : guardCode ⌜GtmplA 1⌝ (CupodV k) (CupodV k) = instB ⌜qCupod⌝ k`
   (the code-level τ of Dupoc's guard: `relabelTemplate_gsubst` + `relabelTemplate_subst`, the
   binary numeral being an `ℒₒᵣ` term code fixed by `termRelabel`), and the search clause
   `cupod_search_V` (fuel 2; the found branch plays `pConst 1`).
2. **Truth equations.** `eval_qCupod_iff_V` in the standard reading `stdActV V`
   ("Cupod plays D against itself"; `qCupod = GtmplA 1 ⇜ ![TD, cl uC, cl wC, …]` with the
   re-valuation terms transposed); `eval_swapActS` pulls the transposed reading `swapActS V`
   back to the standard one (`swapActS V` IS `Structure.lMap swap (stdActS V)`, so this is
   `Semiformula.eval_lMap`), giving `eval_qDupoc_swap_iff_V`/`eval_qCupod_swap_iff_V`: in the
   swapped reading the two formulas exchange roles.
3. **The conjunction family.** `pConj := qDupoc ⋏ qCupod`; `instB` distributes over the code
   connectives (`instB_and/or/neg/imp`), the quote bridges (`quote_and_sentence_V`, …), so
   `instB ⌜pConj⌝ k = instB ⌜qDupoc⌝ k ^⋏ instB ⌜qCupod⌝ k`. **∧-elimination on codes with
   length accounting**: `andLCode`/`andRCode` — one cut on `x ⋏ y` against `{∼x ⋎ ∼y, x}`
   (an `orIntro` over the closed leaf `{∼x, ∼y, ∼x ⋎ ∼y, x}`), exact length by the
   `DlenGraph.*_iff` clauses, bound `a + 8|x| + 4|y| + 7` (resp. `a + 4|x| + 8|y| + 7`), uniform
   `a + 8(|x| + |y|) + 7`. Then `pconj_both_V`: a box of the `k`-instance of `pConj` at any
   budget `a` with `a + 8(…) + 7 ≤ k` makes BOTH searchers find their guards:
   `EvalGraph 2 (DupocV k) … 0 ∧ EvalGraph 2 (CupodV k) … 1`. And `pConj` is true in BOTH
   readings with the same content (`eval_pConj_iff_std`, `eval_pConj_iff_swap`).
4. **The box of the argument.** `gBudget k := ‖k‖ * ‖k‖` (Critch's `g`, `lg k ≺ g(k)`; Σ₁ graph
   `gGraph`), the ℒₒᵣ-core `boxCore : Semisentence ℒₒᵣ 2` — `#0` the CODE slot `n`, `#1` the
   budget `k` — `Box_g χ := boxCoreA ⇜ ![lMap emb ⌜χ⌝, #0]` with the unary Gödel numeral of `χ`
   (a constant; never evaluated), and its semantics `eval_Box_g_iff` in every `LAct`-structure
   whose reduct is standard: `Box_g χ (k) ↔ LenDerivable TAct (gBudget k) (instB ⌜χ⌝ k)`.
   `theta := boxCoreA 🡒 pConjL` (`pConjL := pConj ⇜ ![#1]`), **the convention of
   `tact_parametric_diagonal`: `#0` of `theta` is the code slot, `#1` the budget**, so that
   `theta_subst_code : theta ⇜ ![lMap emb ⌜χ⌝, #0] = Box_g χ 🡒 pConj` (syntactic) and the fixed
   point `psi := tactFixedpoint theta` satisfies `psi_fixed_point : TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj))`.
5. **Σ₁ upward transfer.** `lenDerivable_of_nat : LenDerivable TAct N ⌜σ⌝ (at ℕ) →
   LenDerivable TAct (N : V) ⌜σ⌝` (`lenDerivableDef` is Σ₁, `sigmaOne_upward_absolute`), and
   `lenDerivable_of_proof : TAct ⊢ σ → ∃ N, LenDerivable TAct N ⌜σ⌝` at ℕ (quote the proof,
   `dlen_quote`).
6. **The hypothesis** `BoundedInnerNec d c c₁ c₀` — Critch's Property 4 / assumption (d),
   bounded inner necessitation with a polynomial expansion — definition only.

Trap (`HANDOVER_ARITHMETIZED_S.md` §6): every quote equation below is proved for a VARIABLE
sentence and instantiated; `simp` never sees `⌜qDupoc⌝`, `⌜pConj⌝` or `⌜tactDiag θ⌝` as a closed
term to evaluate.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. Cupod's instance -/

section cupod

/-- The one-variable formula whose `k`-instance is Cupod's guard against itself: the
transposition of `qDupoc`. -/
noncomputable def qCupod : Semisentence LAct 1 := Semiformula.lMap swap qDupoc

lemma lMap_swap_qDupoc : Semiformula.lMap swap qDupoc = qCupod := rfl

lemma lMap_swap_qCupod : Semiformula.lMap swap qCupod = qDupoc := lMap_swap_swap _

lemma coe_quote_sentence₁ (σ : Semisentence LAct 1) : ((⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.coe_quote_eq_quote]

lemma coe_quote_qCupod : ((⌜qCupod⌝ : ℕ) : V) = ⌜qCupod⌝ := coe_quote_sentence₁ _

/-- The meta link of `ArithS.RelabelTemplate` in every model (Σ₁-absoluteness of
`relabelTemplate`), for a VARIABLE semisentence. -/
lemma relabelTemplate_quote_sentence_V (σ : Semisentence LAct 1) :
    relabelTemplate 1 0 (⌜σ⌝ : V) = ⌜Semiformula.lMap swap σ⌝ := by
  have h := DefinedFunction.shigmaOne_absolute_func V (relabelTemplate.defined (V := ℕ))
    (relabelTemplate.defined (V := V)) ![1, 0, (⌜σ⌝ : ℕ)]
  simp only [Function.comp_def, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ, Matrix.vecHead, Matrix.vecTail, Nat.cast_one, Nat.cast_zero] at h
  rw [relabelTemplate_quote_sentence, coe_quote_sentence₁, coe_quote_sentence₁] at h
  exact h.symm

/-- The code-level τ of `⌜qDupoc⌝` is `⌜qCupod⌝`, in every model. -/
lemma relabelTemplate_quote_qDupoc_V : relabelTemplate 1 0 (⌜qDupoc⌝ : V) = ⌜qCupod⌝ :=
  relabelTemplate_quote_sentence_V qDupoc

/-- Cupod's guard code against itself is the code-level τ of Dupoc's. -/
lemma guardCode_CupodV_eq_relabel (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (CupodV k) =
      relabelTemplate 1 0 (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DupocV k)) := by
  have hg0 : IsSemiformula LAct 6 (⌜GtmplA 0⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 0)
  have hg1 : IsSemiformula LAct 6 (⌜GtmplA 1⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA 1)
  rw [← gsubst_of_template hg0, relabelTemplate_gsubst, swapcode_DupocV, relabelTemplate_quote_GtmplA_V,
    swapAct_zero, gsubst_of_template hg1]

/-- **Cupod's instance equation on codes, in every model**: the guard code of `CupodV k` against
itself is the `bnum k`-instance of `⌜qCupod⌝`. -/
theorem guardCode_CupodV_eq_instB (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (CupodV k) = instB (⌜qCupod⌝ : V) k := by
  rw [guardCode_CupodV_eq_relabel, guardCode_DupocV_eq_instB]
  unfold instB
  rw [relabelTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ qDupoc)
    (bnum_cons_semitermVec k), relabelTemplate_quote_qDupoc_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (bnum_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_bnum]

/-- **Cupod's search clause in every model** (fuel `2`): if its guard is provable within the
budget then `CupodV k` defects against itself. -/
theorem cupod_search_V (k : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (CupodV k)) →
      EvalGraph 2 (CupodV k) (CupodV k) (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CupodV k) (CupodV k) (pSearch k (⌜GtmplA 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (CupodV k) (CupodV k) (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- The search clause in the `instB` vocabulary. -/
theorem cupod_search_instB_V (k : V) :
    LenProvableV TAct k (instB (⌜qCupod⌝ : V) k) → EvalGraph 2 (CupodV k) (CupodV k) (CupodV k) 1 := by
  intro h
  rw [← guardCode_CupodV_eq_instB] at h
  exact cupod_search_V k h

end cupod

/-! ### 2. Cupod's truth equation, and the two readings -/

section truth

lemma lMap_swap_TD : Semiterm.lMap swap TD = TD := term_lMap_swap_emb _

/-- The transposed re-valuation terms of Cupod's description. -/
noncomputable def uC : ClosedSemiterm LAct 0 := Semiterm.lMap swap uD
noncomputable def wC : ClosedSemiterm LAct 0 := Semiterm.lMap swap wD

/-- `qCupod` is the template instance `GtmplA 1` filled with Dupoc's description term and the
transposed re-valuation terms. -/
theorem qCupod_eq : qCupod = GtmplA 1 ⇜ ![TD, cl uC, cl wC, TD, cl uC, cl wC] := by
  unfold qCupod qDupoc
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA, swapAct_zero]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TD, lMap_swap_cl, uC, wC]

/-- The transposed descriptions reconstruct `CupodV k` from the canonical code of `DupocV k`. -/
theorem relabel_val_uC_wC_V (k : V) :
    relabel (uC.val (s := stdActV V) ![] Empty.elim) (wC.val (s := stdActV V) ![] Empty.elim)
      (dnum (DupocV k)) = CupodV k := by
  unfold uC wC uD wD
  by_cases h1 : innerD < innerC
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      dnum_of_lt (by rw [swapcode_DupocV]; exact (DupocV_lt_CupodV_iff k).mpr h1)]
    exact swapcode_DupocV k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        dnum_of_gt (by rw [swapcode_DupocV]; exact (CupodV_lt_DupocV_iff k).mpr h2), swapcode_DupocV,
        relabel_zero_one]
    · have h' : innerD = innerC := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      have hDC : DupocV k = CupodV k := by rw [DupocV_eq_inner, CupodV_eq_inner, h']
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, dnum_of_eq (by rw [swapcode_DupocV, hDC]), relabel_zero_one, hDC]

/-- **The truth equation of Cupod's guard in every model** (standard reading): `qCupod` holds at
the budget `k` in `stdActV V` iff `CupodV k` plays `D` against itself (at some fuel). -/
theorem eval_qCupod_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qCupod ↔
      ∃ n, EvalGraph n (CupodV k) (CupodV k) (CupodV k) 1 := by
  rw [qCupod_eq]
  unfold GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TD, cl uC, cl wC, TD, cl uC, cl wC]) =
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TD_V, val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 1]) =
      ![dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim,
        dnum (DupocV k), uC.val (s := stdActV V) ![] Empty.elim, wC.val (s := stdActV V) ![] Empty.elim, 1] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_gtmpl (V := V) _).trans ?_
  simp [relabel_val_uC_wC_V]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- **The transposed reading pulled back**: truth in `swapActS V` (`c_C ↦ 1, c_D ↦ 0`) is truth
of the transposed formula in the standard reading (`swapActS V` is literally the pull-back
`Structure.lMap swap (stdActS V)`, `ArithS.TheoryAct`). -/
theorem eval_swapActS (φ : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim φ ↔
      Semiformula.Eval (s := stdActS V) ![k] Empty.elim (Semiformula.lMap swap φ) :=
  (Semiformula.eval_lMap (s₂ := stdActS V) (Φ := swap)).symm

/-- In the swapped reading, `qDupoc(k)` says "Cupod plays D against itself". -/
theorem eval_qDupoc_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qDupoc ↔
      ∃ n, EvalGraph n (CupodV k) (CupodV k) (CupodV k) 1 := by
  rw [eval_swapActS, lMap_swap_qDupoc, ← stdActV_eq_stdActS]
  exact eval_qCupod_iff_V k

/-- In the swapped reading, `qCupod(k)` says "Dupoc plays C against itself". -/
theorem eval_qCupod_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qCupod ↔
      ∃ n, EvalGraph n (DupocV k) (DupocV k) (DupocV k) 0 := by
  rw [eval_swapActS, lMap_swap_qCupod, ← stdActV_eq_stdActS]
  exact eval_qDupoc_iff_V k

end truth

/-! ### 3. The conjunction family -/

section conj

/-- **The Löb family**: the conjunction of the two guards (Critch 2019 p. 21). -/
noncomputable def pConj : Semisentence LAct 1 := qDupoc ⋏ qCupod

lemma pConj_def : pConj = qDupoc ⋏ qCupod := rfl

lemma lMap_swap_pConj : Semiformula.lMap swap pConj = qCupod ⋏ qDupoc := by
  rw [pConj_def, LogicalConnective.HomClass.map_and, lMap_swap_qDupoc, lMap_swap_qCupod]

/-! #### Quote bridges (for VARIABLE sentences) -/

lemma quote_and_sentence_V {n : ℕ} (φ ψ : Semisentence LAct n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := by
  simp [Sentence.quote_def]

lemma quote_or_sentence_V {n : ℕ} (φ ψ : Semisentence LAct n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := by
  simp [Sentence.quote_def]

lemma quote_neg_sentence_V {n : ℕ} (φ : Semisentence LAct n) : (⌜∼φ⌝ : V) = neg LAct ⌜φ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Semiformula.quote_def, Semiformula.quote_def]
  simp

lemma quote_imp_sentence_V {n : ℕ} (φ ψ : Semisentence LAct n) :
    (⌜φ 🡒 ψ⌝ : V) = Bootstrapping.imp LAct ⌜φ⌝ ⌜ψ⌝ := by
  rw [Sentence.quote_def, Sentence.quote_def, Sentence.quote_def, Semiformula.quote_def,
    Semiformula.quote_def, Semiformula.quote_def]
  simp

/-! #### `instB` distributes over the code connectives -/

lemma instB_and {x y : V} (hx : IsUFormula LAct x) (hy : IsUFormula LAct y) (k : V) :
    instB (x ^⋏ y) k = instB x k ^⋏ instB y k := substs_and hx hy

lemma instB_or {x y : V} (hx : IsUFormula LAct x) (hy : IsUFormula LAct y) (k : V) :
    instB (x ^⋎ y) k = instB x k ^⋎ instB y k := substs_or hx hy

lemma instB_neg {x : V} (hx : IsSemiformula LAct 1 x) (k : V) :
    instB (neg LAct x) k = neg LAct (instB x k) := substs_neg hx (bnum_cons_semitermVec k)

lemma instB_imp {x y : V} (hx : IsSemiformula LAct 1 x) (hy : IsSemiformula LAct 1 y) (k : V) :
    instB (Bootstrapping.imp LAct x y) k = Bootstrapping.imp LAct (instB x k) (instB y k) := by
  unfold Bootstrapping.imp
  rw [instB_or hx.isUFormula.neg hy.isUFormula, instB_neg hx]

/-- The `k`-instance of the code of a conjunction of semisentences. -/
lemma instB_quote_and (φ ψ : Semisentence LAct 1) (k : V) :
    instB (⌜φ ⋏ ψ⌝ : V) k = instB (⌜φ⌝ : V) k ^⋏ instB (⌜ψ⌝ : V) k := by
  rw [quote_and_sentence_V]
  exact instB_and (Sentence.quote_isSemiformul₁ φ).isUFormula (Sentence.quote_isSemiformul₁ ψ).isUFormula k

/-- The `k`-instance of the code of an implication of semisentences. -/
lemma instB_quote_imp (φ ψ : Semisentence LAct 1) (k : V) :
    instB (⌜φ 🡒 ψ⌝ : V) k = Bootstrapping.imp LAct (instB (⌜φ⌝ : V) k) (instB (⌜ψ⌝ : V) k) := by
  rw [quote_imp_sentence_V]
  exact instB_imp (Sentence.quote_isSemiformul₁ φ) (Sentence.quote_isSemiformul₁ ψ) k

/-- **`instB ⌜pConj⌝ k` is the conjunction of the two instances.** -/
theorem instB_quote_pConj (k : V) :
    instB (⌜pConj⌝ : V) k = instB (⌜qDupoc⌝ : V) k ^⋏ instB (⌜qCupod⌝ : V) k :=
  instB_quote_and qDupoc qCupod k

/-! #### ∧-elimination on codes with length accounting -/

section andElim

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

variable (L)

/-- The derivation code of `{x}` from `d : {x ⋏ y}`: weaken `d` to `{x ⋏ y, x}`; introduce
`∼(x ⋏ y) = ∼x ⋎ ∼y` by `orIntro` from the closed leaf `{∼x, ∼y, ∼x ⋎ ∼y, x}`; cut on `x ⋏ y`. -/
noncomputable def andLCode (x y d : V) : V :=
  cutRule {x} (x ^⋏ y)
    (wkRule (insert (x ^⋏ y) {x}) d)
    (orIntro (insert (neg L x ^⋎ neg L y) {x}) (neg L x) (neg L y)
      (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) x))

/-- The derivation code of `{y}` from `d : {x ⋏ y}` (the closed leaf is on `y`). -/
noncomputable def andRCode (x y d : V) : V :=
  cutRule {y} (x ^⋏ y)
    (wkRule (insert (x ^⋏ y) {y}) d)
    (orIntro (insert (neg L x ^⋎ neg L y) {y}) (neg L x) (neg L y)
      (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) y))

variable {L}

/-- The left elimination code is a `T`-proof of `x`. -/
theorem andLCode_proof {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) : Proof T (andLCode L x y d) x := by
  have e₁ : DerivationOf T (wkRule (insert (x ^⋏ y) {x}) d) (insert (x ^⋏ y) {x}) :=
    ⟨by simp, Derivation.wkRule (by simp [hx, hy]) (fun z hz ↦ by simp [mem_singleton_iff.mp hz]) hd⟩
  have e₃ : DerivationOf T
      (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) x)
      (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) :=
    ⟨by simp, Derivation.axL (by simp [hx, hy]) (by simp) (by simp)⟩
  have e₂ : DerivationOf T
      (orIntro (insert (neg L x ^⋎ neg L y) {x}) (neg L x) (neg L y)
        (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) x))
      (insert (neg L x ^⋎ neg L y) {x}) :=
    ⟨by simp, Derivation.orIntro (by simp) e₃⟩
  refine ⟨by simp [andLCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_and hx.isUFormula hy.isUFormula]
  exact e₂

/-- The right elimination code is a `T`-proof of `y`. -/
theorem andRCode_proof {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) : Proof T (andRCode L x y d) y := by
  have e₁ : DerivationOf T (wkRule (insert (x ^⋏ y) {y}) d) (insert (x ^⋏ y) {y}) :=
    ⟨by simp, Derivation.wkRule (by simp [hx, hy]) (fun z hz ↦ by simp [mem_singleton_iff.mp hz]) hd⟩
  have e₃ : DerivationOf T
      (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) y)
      (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) :=
    ⟨by simp, Derivation.axL (by simp [hx, hy]) (by simp) (by simp)⟩
  have e₂ : DerivationOf T
      (orIntro (insert (neg L x ^⋎ neg L y) {y}) (neg L x) (neg L y)
        (axL (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) y))
      (insert (neg L x ^⋎ neg L y) {y}) :=
    ⟨by simp, Derivation.orIntro (by simp) e₃⟩
  refine ⟨by simp [andRCode], Derivation.cutRule e₁ ?_⟩
  rw [neg_and hx.isUFormula hy.isUFormula]
  exact e₂

/-- The exact length of the left elimination code, node by node. -/
theorem dlen_andLCode {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) :
    dlen T (andLCode L x y d) =
      setLen L ({x} : V)
      + (setLen L (insert (x ^⋏ y) {x}) + dlen T d + 1)
      + (setLen L (insert (neg L x ^⋎ neg L y) {x})
          + (setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) + 1) + 1)
      + 1 := by
  apply dlen_eq_of_graph (andLCode_proof hx hy hd).2
  unfold andLCode
  refine DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩, ?_, rfl⟩
  exact DlenGraph.orIntro_iff.mpr ⟨_, DlenGraph.axL_iff.mpr rfl, rfl⟩

/-- The exact length of the right elimination code. -/
theorem dlen_andRCode {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) :
    dlen T (andRCode L x y d) =
      setLen L ({y} : V)
      + (setLen L (insert (x ^⋏ y) {y}) + dlen T d + 1)
      + (setLen L (insert (neg L x ^⋎ neg L y) {y})
          + (setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) + 1) + 1)
      + 1 := by
  apply dlen_eq_of_graph (andRCode_proof hx hy hd).2
  unfold andRCode
  refine DlenGraph.cutRule_iff.mpr ⟨_, _, DlenGraph.wkRule_iff.mpr ⟨_, dlen_graph hd.2, rfl⟩, ?_, rfl⟩
  exact DlenGraph.orIntro_iff.mpr ⟨_, DlenGraph.axL_iff.mpr rfl, rfl⟩

/-- **∧-elimination (left) on codes, sharp**: `dlen (andLCode) ≤ dlen d + 8|x| + 4|y| + 7`. -/
theorem dlen_andLCode_le {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) :
    dlen T (andLCode L x y d) ≤ dlen T d + 8 * formulaLen L x + 4 * formulaLen L y + 7 := by
  have hx' := hx.isUFormula
  have hy' := hy.isUFormula
  set A := formulaLen L x with hA
  set B := formulaLen L y with hB
  have h₁ : setLen L (insert (x ^⋏ y) ({x} : V)) ≤ 2 * A + B + 1 := by
    have := setLen_insert_le (L := L) (x ^⋏ y) {x}
    rw [setLen_singleton, formulaLen_and hx' hy'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₂ : setLen L (insert (neg L x ^⋎ neg L y) ({x} : V)) ≤ 2 * A + B + 1 := by
    have := setLen_insert_le (L := L) (neg L x ^⋎ neg L y) {x}
    rw [setLen_singleton, formulaLen_or hx'.neg hy'.neg, formulaLen_neg hx', formulaLen_neg hy'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₃ : setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) ({x} : V))))
      ≤ 3 * A + 2 * B + 1 := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hx']
    refine le_trans (add_le_add (setLen_insert_le _ _) (le_refl _)) ?_
    rw [formulaLen_neg hy']
    exact le_trans (add_le_add (add_le_add h₂ (le_refl _)) (le_refl _)) (le_of_eq (by ring))
  rw [dlen_andLCode hx hy hd, setLen_singleton]
  calc A
      + (setLen L (insert (x ^⋏ y) {x}) + dlen T d + 1)
      + (setLen L (insert (neg L x ^⋎ neg L y) {x})
          + (setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {x}))) + 1) + 1)
      + 1
      ≤ A + ((2 * A + B + 1) + dlen T d + 1)
      + ((2 * A + B + 1) + ((3 * A + 2 * B + 1) + 1) + 1) + 1 := by gcongr
    _ = dlen T d + 8 * A + 4 * B + 7 := by ring

/-- **∧-elimination (right) on codes, sharp**: `dlen (andRCode) ≤ dlen d + 4|x| + 8|y| + 7`. -/
theorem dlen_andRCode_le {x y d : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (hd : Proof T d (x ^⋏ y)) :
    dlen T (andRCode L x y d) ≤ dlen T d + 4 * formulaLen L x + 8 * formulaLen L y + 7 := by
  have hx' := hx.isUFormula
  have hy' := hy.isUFormula
  set A := formulaLen L x with hA
  set B := formulaLen L y with hB
  have h₁ : setLen L (insert (x ^⋏ y) ({y} : V)) ≤ A + 2 * B + 1 := by
    have := setLen_insert_le (L := L) (x ^⋏ y) {y}
    rw [setLen_singleton, formulaLen_and hx' hy'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₂ : setLen L (insert (neg L x ^⋎ neg L y) ({y} : V)) ≤ A + 2 * B + 1 := by
    have := setLen_insert_le (L := L) (neg L x ^⋎ neg L y) {y}
    rw [setLen_singleton, formulaLen_or hx'.neg hy'.neg, formulaLen_neg hx', formulaLen_neg hy'] at this
    exact le_trans this (le_of_eq (by ring))
  have h₃ : setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) ({y} : V))))
      ≤ 2 * A + 3 * B + 1 := by
    refine le_trans (setLen_insert_le _ _) ?_
    rw [formulaLen_neg hx']
    refine le_trans (add_le_add (setLen_insert_le _ _) (le_refl _)) ?_
    rw [formulaLen_neg hy']
    exact le_trans (add_le_add (add_le_add h₂ (le_refl _)) (le_refl _)) (le_of_eq (by ring))
  rw [dlen_andRCode hx hy hd, setLen_singleton]
  calc B
      + (setLen L (insert (x ^⋏ y) {y}) + dlen T d + 1)
      + (setLen L (insert (neg L x ^⋎ neg L y) {y})
          + (setLen L (insert (neg L x) (insert (neg L y) (insert (neg L x ^⋎ neg L y) {y}))) + 1) + 1)
      + 1
      ≤ B + ((A + 2 * B + 1) + dlen T d + 1)
      + ((A + 2 * B + 1) + ((2 * A + 3 * B + 1) + 1) + 1) + 1 := by gcongr
    _ = dlen T d + 4 * A + 8 * B + 7 := by ring

/-- **∧-elimination (left) on codes, any Δ₁ theory**: from a proof code of `x ⋏ y` of length
`≤ a`, a proof code of `x` of length `≤ a + 8|x| + 4|y| + 7`. -/
theorem lenDerivable_andL_V_sharp {a x y : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (h : LenDerivable T a (x ^⋏ y)) :
    LenDerivable T (a + 8 * formulaLen L x + 4 * formulaLen L y + 7) x := by
  obtain ⟨d, hd, ha⟩ := h
  refine ⟨andLCode L x y d, andLCode_proof hx hy hd, ?_⟩
  refine le_trans (dlen_andLCode_le hx hy hd) ?_
  gcongr

/-- **∧-elimination (right) on codes, any Δ₁ theory**: `a + 4|x| + 8|y| + 7`. -/
theorem lenDerivable_andR_V_sharp {a x y : V} (hx : IsFormula L x) (hy : IsFormula L y)
    (h : LenDerivable T a (x ^⋏ y)) :
    LenDerivable T (a + 4 * formulaLen L x + 8 * formulaLen L y + 7) y := by
  obtain ⟨d, hd, ha⟩ := h
  refine ⟨andRCode L x y d, andRCode_proof hx hy hd, ?_⟩
  refine le_trans (dlen_andRCode_le hx hy hd) ?_
  gcongr

lemma andL_sharp_le_uniform (a x y : V) : a + 8 * x + 4 * y + 7 ≤ a + 8 * (x + y) + 7 := by
  have h : 4 * y ≤ 8 * y :=
    calc 4 * y ≤ 4 * y + 4 * y := le_self_add
      _ = 8 * y := by ring
  calc a + 8 * x + 4 * y + 7 ≤ a + 8 * x + 8 * y + 7 := by gcongr
    _ = a + 8 * (x + y) + 7 := by ring

lemma andR_sharp_le_uniform (a x y : V) : a + 4 * x + 8 * y + 7 ≤ a + 8 * (x + y) + 7 := by
  have h : 4 * x ≤ 8 * x :=
    calc 4 * x ≤ 4 * x + 4 * x := le_self_add
      _ = 8 * x := by ring
  calc a + 4 * x + 8 * y + 7 ≤ a + 8 * x + 8 * y + 7 := by gcongr
    _ = a + 8 * (x + y) + 7 := by ring

end andElim

/-- **∧-elimination (left) on codes at `TAct`, uniform constants `c₁ = 8, c₀ = 7`.** -/
theorem lenDerivable_andL_V {a x y : V} (hx : IsFormula LAct x) (hy : IsFormula LAct y)
    (h : LenDerivable TAct a (x ^⋏ y)) :
    LenDerivable TAct (a + 8 * (formulaLen LAct x + formulaLen LAct y) + 7) x :=
  lenDerivable_mono_V (andL_sharp_le_uniform _ _ _) (lenDerivable_andL_V_sharp hx hy h)

/-- **∧-elimination (right) on codes at `TAct`, uniform constants `c₁ = 8, c₀ = 7`.** -/
theorem lenDerivable_andR_V {a x y : V} (hx : IsFormula LAct x) (hy : IsFormula LAct y)
    (h : LenDerivable TAct a (x ^⋏ y)) :
    LenDerivable TAct (a + 8 * (formulaLen LAct x + formulaLen LAct y) + 7) y :=
  lenDerivable_mono_V (andR_sharp_le_uniform _ _ _) (lenDerivable_andR_V_sharp hx hy h)

/-! #### Both searchers find their guards -/

lemma isFormula_instB_quote (φ : Semisentence LAct 1) (k : V) : IsFormula LAct (instB (⌜φ⌝ : V) k) :=
  isSemiformula_instB (Sentence.quote_isSemiformul₁ φ) k

/-- **Both searchers find their guards from a box of the conjunction**: for every budget `a`
with `a + 8(|instB ⌜qDupoc⌝ k| + |instB ⌜qCupod⌝ k|) + 7 ≤ k`, a `TAct`-proof code of the
`k`-instance of `pConj` of length `≤ a` makes `DupocV k` cooperate with itself and `CupodV k`
defect against itself (fuel 2). -/
theorem pconj_both_V (k : V) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qDupoc⌝ : V) k) + formulaLen LAct (instB (⌜qCupod⌝ : V) k)) + 7 ≤ k →
    LenDerivable TAct a (instB (⌜pConj⌝ : V) k) →
    EvalGraph 2 (DupocV k) (DupocV k) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (CupodV k) (CupodV k) 1 := by
  intro a ha h
  rw [instB_quote_pConj] at h
  have hx := isFormula_instB_quote qDupoc k
  have hy := isFormula_instB_quote qCupod k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy h)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy h)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DupocV_eq_instB] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_eq_instB] at h₂
  exact ⟨dupoc_search_V k h₁, cupod_search_V k h₂⟩

/-! #### `pConj` in both readings -/

/-- `pConj(k)` in the standard reading: Dupoc cooperates with itself AND Cupod defects against
itself. -/
theorem eval_pConj_iff_std (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim pConj ↔
      (∃ n, EvalGraph n (DupocV k) (DupocV k) (DupocV k) 0) ∧
      (∃ n, EvalGraph n (CupodV k) (CupodV k) (CupodV k) 1) := by
  rw [pConj_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDupoc_iff_V, eval_qCupod_iff_V]

/-- `pConj(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pConj_iff_swap (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim pConj ↔
      (∃ n, EvalGraph n (DupocV k) (DupocV k) (DupocV k) 0) ∧
      (∃ n, EvalGraph n (CupodV k) (CupodV k) (CupodV k) 1) := by
  rw [eval_swapActS, lMap_swap_pConj, ← stdActV_eq_stdActS]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDupoc_iff_V, eval_qCupod_iff_V, and_comm]

/-- `pConj(k)` in the standard reading, `stdActS` form. -/
theorem eval_pConj_iff_stdActS (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim pConj ↔
      (∃ n, EvalGraph n (DupocV k) (DupocV k) (DupocV k) 0) ∧
      (∃ n, EvalGraph n (CupodV k) (CupodV k) (CupodV k) 1) := by
  rw [← stdActV_eq_stdActS]; exact eval_pConj_iff_std k

end conj

/-! ### 4. The box formula of the argument, and `θ` -/

section box

/-- Critch's budget function `g`: the square of the bit length, `‖k‖ * ‖k‖` — so that
`C + c·‖k‖ ≤ gBudget k` for all large `k`, whatever the constants. -/
noncomputable def gBudget (k : V) : V := ‖k‖ * ‖k‖

/-- The Σ₁ graph of `gBudget` (`y k`). -/
noncomputable def gGraph : 𝚺₁.Semisentence 2 := .mkSigma “y k. ∃ l, !lengthDef l k ∧ y = l * l”

instance gBudget.defined : 𝚺₁-Function₁[V] gBudget via gGraph := .mk fun v ↦ by
  simp [gGraph, gBudget]

instance gBudget.definable : 𝚺₁-Function₁[V] gBudget := gBudget.defined.to_definable

/-- **The ℒₒᵣ-core of the box**: `n k ↦ ∃ a, a = gBudget k ∧ bewB a n k` —
**`#0` is the CODE slot `n`, `#1` the budget `k`** (the convention of
`tact_parametric_diagonal`, whose right-hand side is `θ ⇜ ![⌜ψ⌝, #0]`). -/
noncomputable def boxCore : Semisentence ℒₒᵣ 2 := “n k. ∃ a, !gGraph a k ∧ !bewBDef a n k”

/-- The core over `LAct`. -/
noncomputable def boxCoreA : Semisentence LAct 2 := Semiformula.lMap emb boxCore

/-- **The box formula of the argument**: `Box_g χ (k) := ∃ a, a = g(k) ∧ bewB a ⌜χ⌝ k`, the
code `⌜χ⌝` written as Foundation's (unary) Gödel numeral — an astronomical CONSTANT, never
evaluated. -/
noncomputable def Box_g (χ : Semisentence LAct 1) : Semisentence LAct 1 :=
  boxCoreA ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0]

lemma Box_g_def (χ : Semisentence LAct 1) :
    Box_g χ = boxCoreA ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0] := rfl

/-- The core at `(n, k)` says `LenDerivable TAct (gBudget k) (instB n k)`. -/
lemma eval_boxCore (n k : V) :
    Semiformula.Eval (s := standardModel V) ![n, k] Empty.elim boxCore ↔
      LenDerivable TAct (gBudget k) (instB n k) := by
  simp [boxCore, bewB]

/-- **The semantics of `Box_g`** in every `LAct`-structure `S` on `V` whose `ℒₒᵣ`-reduct is
standard (`stdActS V`, `swapActS V`, `stdActV V`): `Box_g χ (k)` holds iff the `k`-instance of
`⌜χ⌝` has a `TAct`-proof code of length `≤ gBudget k`. -/
theorem eval_Box_g_iff (χ : Semisentence LAct 1) (S : Structure LAct V)
    (hS : Structure.lMap emb S = standardModel V) (k : V) :
    Semiformula.Eval (s := S) ![k] Empty.elim (Box_g χ) ↔
      LenDerivable TAct (gBudget k) (instB (⌜χ⌝ : V) k) := by
  rw [Box_g_def, Semiformula.eval_substs, val_vec_gödel S hS χ k]
  unfold boxCoreA
  rw [Semiformula.eval_lMap, hS]
  exact eval_boxCore _ _

theorem eval_Box_g_iff_std (χ : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim (Box_g χ) ↔
      LenDerivable TAct (gBudget k) (instB (⌜χ⌝ : V) k) :=
  eval_Box_g_iff χ _ stdActS_lMap_emb k

theorem eval_Box_g_iff_swap (χ : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (Box_g χ) ↔
      LenDerivable TAct (gBudget k) (instB (⌜χ⌝ : V) k) :=
  eval_Box_g_iff χ _ swapActS_lMap_emb k

/-! #### `θ` and its fixed point -/

/-- `pConj` lifted to the two-variable context of `θ` (`#1` = the budget). -/
noncomputable def pConjL : Semisentence LAct 2 := pConj ⇜ ![#1]

/-- **`θ(n, k) := (∃ a, a = g(k) ∧ bewB a n k) 🡒 pConj(k)`** — `#0` the CODE slot `n`, `#1` the
budget `k`. -/
noncomputable def theta : Semisentence LAct 2 := boxCoreA 🡒 pConjL

lemma theta_def : theta = boxCoreA 🡒 pConjL := rfl

/-- A one-variable semisentence is fixed by the identity substitution `![#0]`. -/
lemma subst_bvar_id (φ : Semisentence LAct 1) : φ ⇜ ![#0] = φ := by
  have e : (Rew.subst ![(#0 : Semiterm LAct Empty 1)] : Rew LAct Empty 1 Empty 1) = Rew.id := by
    ext x
    · fin_cases x; simp
    · exact x.elim
  unfold Rewriting.subst
  rw [e, ReflectiveRewriting.id_app]

/-- Filling the code slot of `pConjL` and re-indexing the budget gives `pConj` back. -/
lemma pConjL_subst (t : Semiterm LAct Empty 1) : pConjL ⇜ ![t, #0] = pConj := by
  unfold pConjL Rewriting.subst
  rw [← TransitiveRewriting.comp_app, comp_subst_eq]
  have e : (fun i : Fin 1 ↦ (Rew.subst ![t, (#0 : Semiterm LAct Empty 1)] : Rew LAct Empty 2 Empty 1)
      ((![#1] : Fin 1 → Semiterm LAct Empty 2) i)) = ![(#0 : Semiterm LAct Empty 1)] := by
    funext i; fin_cases i; simp
  rw [e]
  exact subst_bvar_id pConj

/-- **The code slot filled**: `θ ⇜ ![⌜χ⌝, #0] = Box_g χ 🡒 pConj`, syntactically. -/
theorem theta_subst_code (χ : Semisentence LAct 1) :
    theta ⇜ ![Semiterm.lMap emb (⌜χ⌝ : ArithmeticSemiterm Empty 1), #0] = Box_g χ 🡒 pConj := by
  rw [theta_def, Box_g_def]
  unfold Rewriting.subst
  rw [LogicalConnective.HomClass.map_imply]
  congr 1
  exact pConjL_subst _

/-- **The fixed point of the argument**: `psi := tactFixedpoint theta`. -/
noncomputable def psi : Semisentence LAct 1 := tactFixedpoint theta

/-- **`TAct ⊢ ∀ k, psi(k) ↔ (Box_g psi (k) → pConj(k))`** — the parametric diagonal lemma
(`tact_parametric_diagonal₁`) with the code slot resolved by `theta_subst_code`. -/
theorem psi_fixed_point : TAct ⊢ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj)) := by
  have h := tact_parametric_diagonal₁ theta
  rw [theta_subst_code] at h
  exact h

/-- The fixed point holds in every model of `TAct` (soundness). -/
theorem models_psi_fixed_point {M : Type*} [Nonempty M] [Structure LAct M] [M↓[LAct] ⊧* TAct] :
    M↓[LAct] ⊧ ∀¹ (psi 🡘 (Box_g psi 🡒 pConj)) :=
  models_of_provable inferInstance psi_fixed_point

end box

/-! ### 5. Σ₁ upward transfer of a bounded proof -/

section transfer

/-- **Σ₁ upward absoluteness of `LenDerivable`**: a `TAct`-proof code of `⌜σ⌝` of length `≤ N` at
`ℕ` is one in every model of `𝗜𝚺₁` (`lenDerivableDef` is Σ₁). -/
theorem lenDerivable_of_nat (N : ℕ) (σ : Sentence LAct)
    (h : LenDerivable TAct N (⌜σ⌝ : ℕ)) : LenDerivable TAct (N : V) (⌜σ⌝ : V) := by
  have h' : (lenDerivableDef TAct).val.Evalb ![N, (⌜σ⌝ : ℕ)] :=
    ((LenDerivable.defined (V := ℕ) TAct).df _).mpr h
  have h'' := sigmaOne_upward_absolute V (lenDerivableDef TAct) ![N, (⌜σ⌝ : ℕ)] h'
  have e : (Nat.cast ∘ ![N, (⌜σ⌝ : ℕ)] : Fin 2 → V) = ![(N : V), (⌜σ⌝ : V)] := by
    funext i; fin_cases i
    · rfl
    · exact Sentence.coe_quote_eq_quote σ
  rw [e] at h''
  exact ((LenDerivable.defined (V := V) TAct).df _).mp h''

/-- **A `TAct`-theorem has a bounded proof code at `ℕ`**: quote a `Theory.Proof`; the length
is its `mlen` (`dlen_quote`). -/
theorem lenDerivable_of_proof (σ : Sentence LAct) (h : TAct ⊢ σ) :
    ∃ N : ℕ, LenDerivable TAct N (⌜σ⌝ : ℕ) := by
  obtain ⟨b⟩ := h
  refine ⟨mlen (Theory.Proof.toProof2 b), ⌜Theory.Proof.toProof2 b⌝, proof_of_quote_proof2 _, ?_⟩
  rw [dlen_quote]
  exact le_def.mpr (Or.inl rfl)

/-- The two combined: a `TAct`-theorem has, for SOME `N : ℕ`, a proof code of length `≤ N` in
every model of `𝗜𝚺₁`. -/
theorem exists_lenDerivable_V_of_proof (σ : Sentence LAct) (h : TAct ⊢ σ) :
    ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      LenDerivable TAct (N : V) (⌜σ⌝ : V) := by
  obtain ⟨N, hN⟩ := lenDerivable_of_proof σ h
  exact ⟨N, fun V _ _ ↦ lenDerivable_of_nat N σ hN⟩

end transfer

/-! ### 6. The hypothesis: bounded inner necessitation -/

/-- **Bounded inner necessitation with a polynomial expansion — Critch's Property 4 /
assumption (d)** (Critch 2019 §5; `M4_BOUNDED_HBL/BRIEF.md` §6, U5), the ONE named hypothesis
of the PBLT assembly: in every model `V` of `𝗜𝚺₁`, for every one-variable `χ` and every budget
`k : V`, if the `k`-instance of `χ` has a `TAct`-proof code of length `≤ gBudget k` then the
`k`-instance of `Box_g χ` (the sentence "the `k`-instance of `χ` has a proof of length
`≤ g(k)`") has a proof code of length `≤ (gBudget k)^d + c + c₁·(|χ| + ‖k‖) + c₀` — the
expansion `E a = a^d + c` is POLYNOMIAL (`d c : ℕ`), the additive part accounts for the sizes
of the two sentences (`c₁ c₀ : ℕ`). Everything downstream is a theorem GIVEN it; discharging it
for Foundation's calculus with explicit constants is the open research item U10. -/
structure BoundedInnerNec (d c c₁ c₀ : ℕ) : Prop where
  nec : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (χ : Semisentence LAct 1) (k : V),
    LenDerivable TAct (gBudget k) (instB (⌜χ⌝ : V) k) →
    ∃ e : V, e ≤ (gBudget k) ^ d + (c : V) + (c₁ : V) * ((flen (χ : Semiproposition LAct 1) : V) + ‖k‖) + (c₀ : V) ∧
      LenDerivable TAct e (instB (⌜Box_g χ⌝ : V) k)

end ArithS

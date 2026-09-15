import ArithS.Necessitation.NumIdRows
import ArithS.Necessitation.NumId

/-!
# ArithS.Necessitation.Pin — towards `PinKit χ` (`DESIGN_fragments.md` §7.1 steps 1–4 / §7.2)

`Top.lean` §3 states the pinning kit: from the root layout of `x = instB ⌜χ⌝ k` at `&(i+2)`, a list `P`
leaving `instBFact (^&(i + 2 + shiftsV P)) (qNum χ) (bnum k)` in its final context, with `qNum χ =
numeral ⌜χ⌝` — the ONE place the closed code `⌜χ⌝` enters the object proof. This file delivers the
pieces that exist:

* §0 `NumIdTable` — the pin's table (`numIdRows := proRows ++ numIdExtraRows`, `NumIdRows.lean`):
  the prologue table plus the six rows `instBIntro`, `congSubstArg`, `bnumZeroCert`, `bnumOneCert`,
  `bnumEvenCert`, `bnumOddOfEven`; the readings `NumIdTable.<row>` that discharge the generated
  `nok_<row>` hypotheses; `exists_numIdTable`.
* §1 the pin KERNEL `pinKernel_ok`: from `substFact &x &v &y` (the certified substitution), `eqFact &y
  (numeral c)` (`NumId`), `bnumFact &t (bnum k)` and `adjFact &v &t 𝟎` (the vector `bnum k ∷ 0`) in the
  context, the two-step shift-free list `congSubstArg ∷ instBIntro` leaves `instBFact &x (numeral c)
  (bnum k)` — `c` a VARIABLE code, instantiated at `⌜χ⌝` by the assembly.
* §2 the status: what `PinKit.pin` still needs and what `PinKit.cost` cannot get (see the section).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## 0. The pin's table -/

section numIdTable

/-- The pin table: `numIdRowCount` rows at least, the `i`-th with the arity and matrix of `numIdRows[i]`. -/
def NumIdTable (tbl : V) : Prop :=
  (numIdRowCount : V) ≤ len tbl ∧
  ∀ (i : ℕ) (h : i < numIdRows.length),
    rowM tbl.[(i : V)] = ((numIdRows[i]).m : V) ∧ rowB tbl.[(i : V)] = ⌜Semiformula.lMap emb (numIdRows[i]).B⌝

lemma NumIdTable.proTable {tbl : V} (h : NumIdTable tbl) : ProTable tbl := by
  refine ⟨le_trans (by exact_mod_cast (show proRowCount ≤ numIdRowCount by simp only [numIdRowCount]; omega)) h.1, ?_⟩
  intro i hi
  have hi' : i < numIdRows.length := by
    rw [numIdRows_length]; rw [proRows_length] at hi; simp only [numIdRowCount]; omega
  have := h.2 i hi'
  rwa [show numIdRows[i] = proRows[i] from List.getElem_append_left hi] at this

lemma NumIdTable.topTable {tbl : V} (h : NumIdTable tbl) : TopTable tbl := h.proTable.topTable
lemma NumIdTable.layoutTable {tbl : V} (h : NumIdTable tbl) : LayoutTable tbl := h.proTable.layoutTable
lemma NumIdTable.walkTable {tbl : V} (h : NumIdTable tbl) : WalkTable tbl := h.proTable.walkTable

/-- The reading of the `k`-th extra row (what `nok_<row>` takes). -/
lemma NumIdTable.extra {tbl : V} (h : NumIdTable tbl) (k : ℕ) (hk : k < numIdExtraRowCount) :
    ((proRowCount + k : ℕ) : V) < len tbl ∧
    rowM tbl.[((proRowCount + k : ℕ) : V)] = ((numIdExtraRows[k]'(by rw [numIdExtraRows_length]; exact hk)).m : V) ∧
    rowB tbl.[((proRowCount + k : ℕ) : V)] =
      ⌜Semiformula.lMap emb (numIdExtraRows[k]'(by rw [numIdExtraRows_length]; exact hk)).B⌝ := by
  have hlt : proRowCount + k < numIdRows.length := by rw [numIdRows_length]; simp only [numIdRowCount]; omega
  have hr := h.2 (proRowCount + k) hlt
  have hk' : k < numIdExtraRows.length := by rw [numIdExtraRows_length]; exact hk
  have e' : numIdRows[proRowCount + k]? = numIdExtraRows[k]? := by
    unfold numIdRows
    rw [List.getElem?_append_right (by rw [proRows_length]; omega), proRows_length, Nat.add_sub_cancel_left]
  have e : numIdRows[proRowCount + k]'hlt = numIdExtraRows[k]'hk' := by
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hk'] at e'
    exact Option.some.inj e'
  rw [e] at hr
  exact ⟨lt_of_lt_of_le (by exact_mod_cast hlt) (numIdRows_length ▸ h.1), hr.1, hr.2⟩

lemma NumIdTable.instBIntro {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_instBIntro : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_instBIntro : ℕ) : V)] = ((5 : ℕ) : V) ∧
    rowB tbl.[((nIdx_instBIntro : ℕ) : V)] = impChainV LAct (vecOf row_instBIntro_as) row_instBIntro_c := by
  have := h.extra 0 (by decide)
  have e : ((nIdx_instBIntro : ℕ) : V) = ((proRowCount + 0 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_instBIntro

lemma NumIdTable.congSubstArg {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_congSubstArg : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_congSubstArg : ℕ) : V)] = ((4 : ℕ) : V) ∧
    rowB tbl.[((nIdx_congSubstArg : ℕ) : V)] = impChainV LAct (vecOf row_congSubstArg_as) row_congSubstArg_c := by
  have := h.extra 1 (by decide)
  have e : ((nIdx_congSubstArg : ℕ) : V) = ((proRowCount + 1 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_congSubstArg

lemma NumIdTable.bnumZeroCert {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_bnumZeroCert : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_bnumZeroCert : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumZeroCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumZeroCert_as) row_bnumZeroCert_c := by
  have := h.extra 2 (by decide)
  have e : ((nIdx_bnumZeroCert : ℕ) : V) = ((proRowCount + 2 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_bnumZeroCert

lemma NumIdTable.bnumOneCert {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_bnumOneCert : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_bnumOneCert : ℕ) : V)] = ((1 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumOneCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumOneCert_as) row_bnumOneCert_c := by
  have := h.extra 3 (by decide)
  have e : ((nIdx_bnumOneCert : ℕ) : V) = ((proRowCount + 3 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_bnumOneCert

lemma NumIdTable.bnumEvenCert {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_bnumEvenCert : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_bnumEvenCert : ℕ) : V)] = ((9 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumEvenCert : ℕ) : V)] = impChainV LAct (vecOf row_bnumEvenCert_as) row_bnumEvenCert_c := by
  have := h.extra 4 (by decide)
  have e : ((nIdx_bnumEvenCert : ℕ) : V) = ((proRowCount + 4 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_bnumEvenCert

lemma NumIdTable.bnumOddOfEven {tbl : V} (h : NumIdTable tbl) :
    ((nIdx_bnumOddOfEven : ℕ) : V) < len tbl ∧
    rowM tbl.[((nIdx_bnumOddOfEven : ℕ) : V)] = ((6 : ℕ) : V) ∧
    rowB tbl.[((nIdx_bnumOddOfEven : ℕ) : V)] = impChainV LAct (vecOf row_bnumOddOfEven_as) row_bnumOddOfEven_c := by
  have := h.extra 5 (by decide)
  have e : ((nIdx_bnumOddOfEven : ℕ) : V) = ((proRowCount + 5 : ℕ) : V) := rfl
  rw [e]
  refine ⟨this.1, this.2.1, ?_⟩
  rw [impChainV_vecOf, this.2.2]
  exact quote_row_bnumOddOfEven

/-- **A sound pin table exists in every model**, with one standard length bound. -/
theorem exists_numIdTable : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ NumIdTable tbl := by
  obtain ⟨N, hN⟩ := exists_rows numIdRows
  refine ⟨N, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ?_, ?_⟩
  · rw [len_vecOf, hlen, numIdRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'

end numIdTable

/-! ## 1. The pin kernel: `congSubstArg` then `instBIntro` -/

section kernel

/-- The two kernel steps. -/
noncomputable def pinKernelSteps (W x y v t c k : V) : V :=
  ?[mkStep W ((nIdx_congSubstArg : ℕ) : V) ?[^&x, ^&v, ^&y, numeral c],
    mkStep W ((nIdx_instBIntro : ℕ) : V) ?[numeral c, bnum k, ^&t, ^&v, ^&x]]

/-- **The pin kernel.** In a context holding `substFact &x &v &y` (the certified substitution
`&x = subst &v &y`), `eqFact &y (numeral c)` (the numeral identification of the source), `bnumFact &t
(bnum k)` (the certified binary numeral) and `adjFact &v &t 𝟎` (the substitution vector), the two Horn
steps `congSubstArg [numeral c, &y, &v, &x]` and `instBIntro [numeral c, bnum k, &t, &v, &x]` are
applicable at cap `9`, shift-free, and leave `instBFact &x (numeral c) (bnum k)`. -/
theorem pinKernel_ok {tbl N E Γ W x y v t c k : V} (htbl : TableOK tbl N) (hT : NumIdTable tbl)
    (hWp : W = numIdPieces) (hΓ : IsFormulaSet LAct Γ)
    (hEx : x + 1 ≤ E) (hEy : y + 1 ≤ E) (hEv : v + 1 ≤ E) (hEt : t + 1 ≤ E)
    (hEc : 2 * c + 1 ≤ E) (hEk : termLen LAct (bnum k) ≤ E)
    (hs : neg LAct (substFact (^&x) (^&v) (^&y)) ∈ Γ) (hy : neg LAct (eqFact (^&y) (numeral c)) ∈ Γ)
    (hb : neg LAct (bnumFact (^&t) (bnum k)) ∈ Γ) (ha : neg LAct (adjFact (^&v) (^&t) (𝟎 : V)) ∈ Γ) :
    ListOK tbl E ((9 : ℕ) : V) Γ (pinKernelSteps W x y v t c k) ∧ NoDrop' (pinKernelSteps W x y v t c k) ∧
    shiftsV (pinKernelSteps W x y v t c k) = 0 ∧ len (pinKernelSteps W x y v t c k) = 2 ∧
    SizeOK 0 0 (pinKernelSteps W x y v t c k) ∧
    neg LAct (instBFact (^&x) (numeral c) (bnum k)) ∈ finalCtx Γ (pinKernelSteps W x y v t c k) := by
  unfold pinKernelSteps
  have hnc : IsSemiterm LAct 0 (numeral c) := isSemiterm_numeral_LAct c
  have hEnc : termLen LAct (numeral c) ≤ E := termLen_numeral_le' hEc
  have hbk : IsSemiterm LAct 0 (bnum k) := bnum_term_LAct k
  obtain ⟨hr1, hr2, hr3⟩ := hT.congSubstArg
  obtain ⟨hi1, hi2, hi3⟩ := hT.instBIntro
  obtain ⟨ok1, tag1, ctx1⟩ := nok_congSubstArg htbl hWp hr1 ⟨hr2, hr3⟩ hΓ (by simp) (termLen_fvar_le hEx)
    (by simp) (termLen_fvar_le hEv) (by simp) (termLen_fvar_le hEy) hnc hEnc hy hs
  have hΓ₁ : IsFormulaSet LAct (ctxAfter Γ (mkStep W ((nIdx_congSubstArg : ℕ) : V) ?[^&x, ^&v, ^&y, numeral c])) :=
    isFormulaSet_ctxAfter 8 htbl ok1
  rw [ctx1] at hΓ₁
  obtain ⟨ok2, tag2, ctx2⟩ := nok_instBIntro htbl hWp hi1 ⟨hi2, hi3⟩ hΓ₁ hnc hEnc hbk hEk (by simp) (termLen_fvar_le hEt)
    (by simp) (termLen_fvar_le hEv) (by simp) (termLen_fvar_le hEx)
    (mem_insert_of_mem' hb) (mem_insert_of_mem' ha) mem_insert_self'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine listOK_cons (ok1.mono (by exact_mod_cast (by decide : 8 ≤ 9))) ?_
    rw [ctx1]
    exact listOK_single (ok2.mono (by exact_mod_cast (by decide : 8 ≤ 9)))
  · exact noDrop'_cons (Or.inl tag1) (noDrop'_single (Or.inl tag2))
  · rw [shiftsV_cons_tag0 tag1, shiftsV_single_tag0 tag2]
  · simp [one_add_one_eq_two]
  · exact sizeOK_cons (Or.inl tag1) (sizeOK_single (Or.inl tag2))
  · rw [finalCtx_cons, finalCtx_single, ctx1, ctx2]
    exact mem_insert_self'

end kernel

end ArithS

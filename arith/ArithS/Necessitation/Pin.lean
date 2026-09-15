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
* §2 the assembly `pin_assembly`: from the root layout and TWO producer ORACLES (`BnumOracle` — the
  bit-wise certification of `bnum k`; `SubstOracle` — `certSubst` for `bnum k ∷ 0` re-indexed), the list
  `describeF ⌜χ⌝ ++ vector walk ++ Pb ++ numId ++ Ps ++ kernel` with every `pin` conjunct of `PinKit χ`
  EXCEPT the cost, for an explicit standard `Cχ`.
* §3 the status: what remains for `PinKit.pin`, and why `PinKit.cost` as stated cannot be met.
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

/-! ## 2. The assembly: `PinKit.pin` from two producer ORACLES

The pin's list is `describeF ⌜χ⌝ ++ (vector walk of bnum k ∷ 0) ++ Pb ++ numId ++ Ps ++ kernel`. Two
producers do not exist yet and enter as ORACLES, stated exactly at the interface their producers will
have (`DESIGN_fragments.md` §7.1 step 1 / `Cert.certSubst_ok` re-indexed through `reidxL`):

* `BnumOracle` — the certification of the binary numeral along the bits of `k` (rows
  `bnumZeroCert`/`bnumOneCert`/`bnumEvenCert`/`bnumOddOfEven`, now in the table): from the term dossier of
  `bnum k` at `&j`, a cut-admitting list of `≤ Cb·(‖k‖+1)` eigenvariables leaving `bnumFact &(j+σ) (bnum k)`.
* `SubstOracle` — `certSubst` for the vector `bnum k ∷ 0` and the source `⌜χ⌝`, re-indexed: from the three
  dossiers (source at `&y`, image `instB ⌜χ⌝ k` at `&x`, vector at `&iw`) a list leaving `substFact &(x+σ)
  &(iw+σ) &(y+σ)`. `certSubst_ok` delivers it under `SubFPre` and the `qWalkP` length bound; discharging
  those for THIS vector (its `Q` is `≥ |bnum k|`) is the remaining `Cert`-side work.

Given the two, `pin_assembly` proves the `pin` conjuncts of `PinKit χ` EXCEPT the cost — see §3.
-/

section assembly

/-- The binary-numeral certification oracle (§7.1 step 1). -/
def BnumOracle (tbl E k : V) (Cb : ℕ) : Prop :=
  ∀ {Γ j : V}, IsFormulaSet LAct Γ → DossT walkPieces Γ 0 (bnum k) j → (Cb : V) * (‖k‖ + j + 1) ≤ E →
    ∃ Pb : V, ListOK tbl E ((9 : ℕ) : V) Γ Pb ∧ NoDrop' Pb ∧ shiftsV Pb ≤ (Cb : V) * (‖k‖ + 1) ∧
      neg LAct (bnumFact (^&(j + shiftsV Pb)) (bnum k)) ∈ finalCtx Γ Pb

/-- The certified-substitution oracle (`certSubst` re-indexed, for `w = bnum k ∷ 0` and the source `⌜χ⌝`). -/
def SubstOracle (tbl E : V) (χ : Semisentence LAct 1) (k : V) (Cs : ℕ) : Prop :=
  ∀ {Γ y x iw : V}, IsFormulaSet LAct Γ → DossF walkPieces Γ 1 (⌜χ⌝ : V) y →
    DossF walkPieces Γ 0 (instB (⌜χ⌝ : V) k) x → DossV walkPieces Γ 0 1 (bnum k ∷ 0) 1 iw →
    (Cs : V) * (‖k‖ + x + y + iw + 1) ≤ E →
    ∃ Ps : V, ListOK tbl E ((9 : ℕ) : V) Γ Ps ∧ NoDrop' Ps ∧ shiftsV Ps ≤ (Cs : V) * (‖k‖ + 1) ∧
      neg LAct (substFact (^&(x + shiftsV Ps)) (^&(iw + shiftsV Ps)) (^&(y + shiftsV Ps))) ∈ finalCtx Γ Ps

/-! ### 2.1 Transport of the four kernel facts through a cut-admitting list -/

/-- Iterated shift of a two-argument fact, for a VARIABLE predicate code `P` (the big quote `Pbnum` must not
enter a `definability` motive). -/
lemma shiftIterV_fact2 {P a b : V} (hP : IsSemiformula LAct ((2 : ℕ) : V) P) (hs : shift LAct P = P)
    (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    ∀ c : V, shiftIterV (subst LAct (listToVec [a, b]) P) c =
      subst LAct (listToVec [termShiftIterV a c, termShiftIterV b c]) P := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => rw [shiftIterV_zero, termShiftIterV_zero, termShiftIterV_zero]
  | succ c ih =>
    rw [shiftIterV_succ, ih, shift_subst_listToVec [termShiftIterV a c, termShiftIterV b c] (by simpa using hP) hs (n := 0)
      (List.forall_mem_cons.mpr ⟨isSemiterm_termShiftIterV ha c,
        List.forall_mem_cons.mpr ⟨isSemiterm_termShiftIterV hb c, List.forall_mem_nil _⟩⟩)]
    simp only [List.map_cons, List.map_nil, termShiftIterV_succ]

lemma shiftIterV_bnumFact {t k : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) (c : V) :
    shiftIterV (bnumFact t k) c = bnumFact (termShiftIterV t c) (termShiftIterV k c) :=
  shiftIterV_fact2 isSemiformula_Pbnum shift_Pbnum ht hk c

lemma termShiftIterV_numeral (x : V) : ∀ c : V, termShiftIterV (numeral x) c = numeral x := by
  intro c
  induction c using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ c ih => rw [termShiftIterV_succ, ih, termShift_numeral_LAct]

lemma transport_bnum {Γ S t k : V} (hS : NoDrop' S) (h : neg LAct (bnumFact (^&t) (bnum k)) ∈ Γ) :
    neg LAct (bnumFact (^&(t + shiftsV S)) (bnum k)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_bnumFact (by simp) (bnum_term_LAct k)), shiftIterV_bnumFact (by simp) (bnum_term_LAct k),
    termShiftIterV_fvar, termShiftIterV_bnum] at this

lemma transport_adj {Γ S v t : V} (hS : NoDrop' S) (h : neg LAct (adjFact (^&v) (^&t) (𝟎 : V)) ∈ Γ) :
    neg LAct (adjFact (^&(v + shiftsV S)) (^&(t + shiftsV S)) (𝟎 : V)) ∈ finalCtx Γ S := by
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_adjFact (by simp) (by simp) h0), shiftIterV_adjFact (by simp) (by simp) h0,
    termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_qqZero] at this

lemma transport_eq {Γ S y c : V} (hS : NoDrop' S) (h : neg LAct (eqFact (^&y) (numeral c)) ∈ Γ) :
    neg LAct (eqFact (^&(y + shiftsV S)) (numeral c)) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  have e : eqFact (^&y) (numeral c) = eqFactB (^&y) (numeral c) := rfl
  rw [e] at this
  rwa [shiftIterV_neg (isFormula_eqFactB (by simp) (isSemiterm_numeral_LAct c)),
    shiftIterV_eqFactB (by simp) (isSemiterm_numeral_LAct c), termShiftIterV_fvar, termShiftIterV_numeral] at this

lemma transport_subst {Γ S x v y : V} (hS : NoDrop' S) (h : neg LAct (substFact (^&x) (^&v) (^&y)) ∈ Γ) :
    neg LAct (substFact (^&(x + shiftsV S)) (^&(v + shiftsV S)) (^&(y + shiftsV S))) ∈ finalCtx Γ S := by
  have := mem_finalCtx_of_mem' hS h
  rwa [shiftIterV_neg (isFormula_substFact (by simp) (by simp) (by simp)), shiftIterV_substFact (by simp) (by simp) (by simp),
    termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_fvar] at this

/-! ### 2.2 The cap arithmetic -/

lemma lin_add {a b : ℕ} {u v w : V} (hu : u ≤ (a : V) * w) (hv : v ≤ (b : V) * w) : u + v ≤ ((a + b : ℕ) : V) * w := by
  push_cast; rw [add_mul]; exact add_le_add hu hv

lemma lin_const {c : ℕ} {w : V} (hw : 1 ≤ w) : (c : V) ≤ (c : V) * w :=
  le_mul_of_one_le_right (by simp) hw

lemma lin_mono {a b : ℕ} {u w : V} (hab : a ≤ b) (hu : u ≤ (a : V) * w) : u ≤ (b : V) * w :=
  le_trans hu (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by simp))

lemma lin_one {w : V} (hw : 1 ≤ w) : (1 : V) ≤ ((1 : ℕ) : V) * w := by
  push_cast; rw [one_mul]; exact hw

lemma lin_two {w : V} (hw : 1 ≤ w) : (2 : V) ≤ ((2 : ℕ) : V) * w := by
  push_cast; exact le_mul_of_one_le_right (by norm_num) hw

/-- The master cap: `z ≤ A·(‖k‖+1) + A·i ≤ Cχ·(‖k‖+i+1) ≤ E`. -/
lemma cap_master {A Cχ : ℕ} {k i E z : V} (hA : A ≤ Cχ) (h : (Cχ : V) * (‖k‖ + i + 1) ≤ E)
    (hz : z ≤ (A : V) * (‖k‖ + 1) + (A : V) * i) : z ≤ E := by
  refine le_trans hz (le_trans ?_ h)
  rw [show (A : V) * (‖k‖ + 1) + (A : V) * i = (A : V) * (‖k‖ + i + 1) by ring]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA) (by simp)

/-- A quantity `≤ A·(‖k‖+1) + i` (offsets carry one `i`). -/
lemma cap_master' {A Cχ : ℕ} {k i E z : V} (hA1 : 1 ≤ A) (hA : A ≤ Cχ) (h : (Cχ : V) * (‖k‖ + i + 1) ≤ E)
    (hz : z ≤ (A : V) * (‖k‖ + 1) + i) : z ≤ E :=
  cap_master hA h (le_trans hz (add_le_add (le_refl _) (le_mul_of_one_le_left (by simp) (by exact_mod_cast hA1))))

/-! ### 2.3 The assembly -/

set_option maxHeartbeats 2000000 in
/-- **The assembly.** Given the two oracles, the `pin` conjuncts of `PinKit χ` except the cost: from the
root layout of `instB ⌜χ⌝ k` at `&i`, a list `P` applicable at cap `9`, cut-admitting, with
`shiftsV P ≤ Cχ·(‖k‖+1)`, leaving `instBFact &(i + 2 + shiftsV P) (qNum χ) (bnum k)`. -/
theorem pin_assembly (χ : Semisentence LAct 1) (Cb Cs : ℕ) :
    ∃ Cχ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ i k : V},
      TableOK tbl N → NumIdTable tbl → IsFormulaSet LAct Γ → RootLayout Γ (instB (⌜χ⌝ : V) k) i →
      BnumOracle tbl E k Cb → SubstOracle tbl E χ k Cs → (Cχ : V) * (‖k‖ + i + 1) ≤ E →
      ∃ P : V, ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ shiftsV P ≤ (Cχ : V) * (‖k‖ + 1) ∧
        neg LAct (instBFact (^&(i + 2 + shiftsV P)) (qNum χ) (bnum k)) ∈ finalCtx Γ P := by
  obtain ⟨Cn, hCn⟩ := numId_sentence χ
  obtain ⟨fχ, hfχ⟩ : ∃ f : ℕ, f = flN (⌜χ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨qχ, hqχ⟩ : ∃ q : ℕ, q = (⌜χ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 40 * (fχ + Cn + Cb + qχ + 1) := ⟨_, rfl⟩
  obtain ⟨Cχ, hCχ⟩ : ∃ C : ℕ, C = A * (Cs + 1) := ⟨_, rfl⟩
  refine ⟨Cχ, ?_⟩
  intro V _ _ tbl N E Γ i k htbl hT hΓ hR hB hS hE
  have hW : WalkTable tbl := hT.walkTable
  have hu1 : (1 : V) ≤ ‖k‖ + 1 := le_add_self
  -- the standard quantities of χ in V
  have hfV : formulaLen LAct (⌜χ⌝ : V) = (fχ : V) := by
    rw [hfχ, ← Sentence.coe_quote_eq_quote (V := V) χ, flN_cast]
  have hqV : ((qχ : ℕ) : V) = ⌜χ⌝ := by rw [hqχ]; exact Sentence.coe_quote_eq_quote χ
  have hr : IsSemiformula LAct (1 : V) (⌜χ⌝ : V) := Sentence.quote_isSemiformul₁ χ
  have hlenk : termLen LAct (bnum k) ≤ 6 * ‖k‖ + 1 := termLen_bnum_le_bk le_rfl
  have hAC : A ≤ Cχ := by rw [hCχ]; exact Nat.le_mul_of_pos_right A (by omega)
  have hACs : A + Cs ≤ Cχ := by
    rw [hCχ]
    calc A + Cs ≤ A + A * Cs := add_le_add (le_refl _) (Nat.le_mul_of_pos_left Cs (by omega))
      _ = A * (Cs + 1) := by ring
  -- ===== block 1: the walk of χ
  have cap1 : 2 * (1 : V) + 2 * formulaLen LAct (⌜χ⌝ : V) + 8 ≤ E := by
    rw [hfV]
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc 2 * (1 : V) + 2 * (fχ : V) + 8 = ((2 * fχ + 10 : ℕ) : V) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (lin_const hu1)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  obtain ⟨ok₁, nd₁, sh₁, cnt₁, _⟩ := describeF_ok htbl hW hr cap1 hΓ
  set S₁ := describeF walkPieces 1 (⌜χ⌝ : V) with hS₁
  set cχ := descCountF walkPieces 1 (⌜χ⌝ : V) with hcχ
  set Γ₁ := finalCtx Γ S₁ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ ok₁
  have hcχle : cχ ≤ (2 * fχ : ℕ) * (‖k‖ + 1) := by
    have : cχ + 1 ≤ 2 * (fχ : V) := by rw [← hfV]; exact cnt₁
    push_cast
    exact le_trans (le_trans le_self_add this) (le_mul_of_one_le_right (by simp) hu1)
  have hDχ₁ : DossF walkPieces Γ₁ 1 (⌜χ⌝ : V) 0 := dossF_of_walk nd₁
  have hR₁ : RootLayout Γ₁ (instB (⌜χ⌝ : V) k) (i + cχ) := by
    have := hR.transport nd₁.noDrop'; rwa [sh₁] at this
  -- ===== block 2: the vector walk of w = bnum k ∷ 0
  set w : V := bnum k ∷ 0 with hwdef
  have hw : IsSemitermVec LAct ((0 : V) + 1) (0 : V) w :=
    IsSemitermVec.adjoin (IsSemitermVec.nil (L := LAct) (0 : V)) (bnum_term_LAct k)
  have hw' : IsSemitermVec LAct (1 : V) (0 : V) w := by rwa [zero_add] at hw
  have hlenw : listSum (termLenVec LAct 1 w) = termLen LAct (bnum k) := by
    rw [hwdef, show (1 : V) = 0 + 1 by rw [zero_add],
      termLenVec_cons (bnum_term_LAct k).isUTerm (IsSemitermVec.nil (L := LAct) (0 : V)).isUTerm, termLenVec_nil,
      listSum_adjoin, listSum_nil, add_zero]
  have cap2 : 2 * (0 : V) + 2 * listSum (termLenVec LAct 1 w) + 8 ≤ E := by
    rw [hlenw]
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc 2 * (0 : V) + 2 * termLen LAct (bnum k) + 8 ≤ 2 * 0 + 2 * (6 * ‖k‖ + 1) + 8 :=
          add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hlenk (by simp))) (le_refl _)
      _ = 12 * ‖k‖ + 10 := by ring
      _ ≤ 12 * ‖k‖ + 12 := add_le_add (le_refl _) (by norm_num)
      _ = ((12 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (le_refl _)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  have ih : ∀ m < (1 : V), TermOK tbl walkPieces 0 w.[m] := fun m hm ↦ termOK_of_isSemiterm htbl hW rfl 0 _ (hw'.nth hm)
  obtain ⟨_, hcnt₂, hVF⟩ := descVecAux_ok htbl hW rfl (by norm_num : (1 : V) ≤ 2) hw' ih cap2 1 le_rfl
  obtain ⟨ok₂, nd₂, sh₂, _⟩ := hVF Γ₁ hΓ₁
  set S₂ := π₂ (descVecAux walkPieces 0 (descTVec walkPieces 0 1 w) 1) with hS₂
  set cw := π₁ (descVecAux walkPieces 0 (descTVec walkPieces 0 1 w) 1) with hcw
  set Γ₂ := finalCtx Γ₁ S₂ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 8 htbl hΓ₁ ok₂
  have hlw : len w = 1 := by rw [hwdef, len_adjoin, len_nil, zero_add]
  have hcwle : cw ≤ ((14 : ℕ) : V) * (‖k‖ + 1) := by
    have htl : takeLast w 1 = w := by have := takeLast_len_self w; rwa [hlw] at this
    have h2 := hcnt₂
    rw [htl, hlenw] at h2
    calc cw ≤ 2 * termLen LAct (bnum k) := h2
      _ ≤ 2 * (6 * ‖k‖ + 1) := mul_le_mul_of_nonneg_left hlenk (by simp)
      _ = 12 * ‖k‖ + 2 := by ring
      _ ≤ 14 * ‖k‖ + 14 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (by simp)) (by norm_num)
      _ = ((14 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
  have hDw₂ : DossV walkPieces Γ₂ 0 1 w 1 0 := dossV_of_walk nd₂
  have hDχ₂ : DossF walkPieces Γ₂ 1 (⌜χ⌝ : V) cw := by
    have := dossF_transport' nd₂.noDrop' hDχ₁; rwa [sh₂, zero_add] at this
  have hR₂ : RootLayout Γ₂ (instB (⌜χ⌝ : V) k) (i + cχ + cw) := by
    have := hR₁.transport nd₂.noDrop'; rwa [sh₂] at this
  -- the entry's dossier (the term `bnum k` at `&1`) and the adj fact `&0 = &1 ∷ 𝟎`
  have hDw₂' : DossV walkPieces Γ₂ 0 1 w ((0 : V) + 1) 0 := by rw [zero_add]; exact hDw₂
  obtain ⟨ha₂, _, hDt₂, _⟩ := dossV_succ htbl hW rfl hw' (by rw [zero_add]) hDw₂'
  have e10 : (1 : V) - ((0 : V) + 1) = 0 := by rw [zero_add]; exact tsub_eq_zero_of_le (le_refl _)
  rw [e10, hwdef, nth_adjoin_zero, zero_add] at hDt₂
  rw [vRef_zero, zero_add] at ha₂
  -- ===== block 3: the binary numeral certification (oracle)
  have cap3 : (Cb : V) * (‖k‖ + 1 + 1) ≤ E := by
    refine cap_master (A := 2 * Cb) (by omega) hE ?_
    calc (Cb : V) * (‖k‖ + 1 + 1) ≤ (Cb : V) * (2 * (‖k‖ + 1)) :=
          mul_le_mul_of_nonneg_left (by rw [two_mul]; exact add_le_add (le_refl _) hu1) (by simp)
      _ = ((2 * Cb : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ ((2 * Cb : ℕ) : V) * (‖k‖ + 1) + ((2 * Cb : ℕ) : V) * i := le_self_add
  obtain ⟨Pb, okb, ndb, shb, hbf⟩ := hB hΓ₂ hDt₂ cap3
  set σb := shiftsV Pb with hσb
  set Γ₃ := finalCtx Γ₂ Pb with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 9 htbl hΓ₂ okb
  have ha₃ : neg LAct (adjFact (^&σb) (^&(1 + σb)) (𝟎 : V)) ∈ Γ₃ := by
    have := transport_adj ndb ha₂; rwa [zero_add] at this
  have hDχ₃ : DossF walkPieces Γ₃ 1 (⌜χ⌝ : V) (cw + σb) := dossF_transport' ndb hDχ₂
  have hDw₃ : DossV walkPieces Γ₃ 0 1 w 1 σb := by
    have := dossV_transport' ndb hDw₂; rwa [zero_add] at this
  have hR₃ : RootLayout Γ₃ (instB (⌜χ⌝ : V) k) (i + cχ + cw + σb) := hR₂.transport ndb
  -- ===== block 4: the numeral identification of χ (NumId)
  have cap4 : (Cn : V) + (cw + σb) ≤ E := by
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc (Cn : V) + (cw + σb) ≤ (Cn : V) * (‖k‖ + 1) + (((14 : ℕ) : V) * (‖k‖ + 1) + (Cb : V) * (‖k‖ + 1)) :=
          add_le_add (lin_const hu1) (add_le_add hcwle shb)
      _ = ((Cn + 14 + Cb : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (le_refl _)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  obtain ⟨Pn, hPn⟩ := hCn V htbl hT.layoutTable hΓ₃ (by rw [Nat.cast_one]; exact hDχ₃) cap4
  set Γ₄ := finalCtx Γ₃ Pn with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := hPn.isFormulaSet htbl hΓ₃
  have hy₄ : neg LAct (eqFact (^&(cw + σb)) (numeral (⌜χ⌝ : V))) ∈ Γ₄ := hPn.2.2.2.2.2
  have hbf₄ := hPn.mem hbf
  have ha₄ := hPn.mem ha₃
  have hDχ₄ : DossF walkPieces Γ₄ 1 (⌜χ⌝ : V) (cw + σb) := hPn.dossF hDχ₃
  have hDw₄ : DossV walkPieces Γ₄ 0 1 w 1 σb := hPn.dossV hDw₃
  have hR₄ : RootLayout Γ₄ (instB (⌜χ⌝ : V) k) (i + cχ + cw + σb) := by
    have := hR₃.transport hPn.2.1; rwa [hPn.2.2.1, add_zero] at this
  have hDx₄ : DossF walkPieces Γ₄ 0 (instB (⌜χ⌝ : V) k) (i + cχ + cw + σb + 2) := hR₄.1
  -- ===== block 5: the certified substitution (oracle)
  have hin : ‖k‖ + (i + cχ + cw + σb + 2) + (cw + σb) + σb + 1 ≤ ((2 * fχ + 3 * Cb + 33 : ℕ) : V) * (‖k‖ + 1) + i := by
    have h1 : ‖k‖ ≤ ((1 : ℕ) : V) * (‖k‖ + 1) := by push_cast; rw [one_mul]; exact le_self_add
    have hsum : ‖k‖ + cχ + cw + σb + 2 + cw + σb + σb + 1 ≤ ((2 * fχ + 3 * Cb + 33 : ℕ) : V) * (‖k‖ + 1) :=
      lin_mono (by omega) (lin_add (lin_add (lin_add (lin_add (lin_add (lin_add (lin_add (lin_add h1 hcχle) hcwle) shb)
        (lin_two hu1)) hcwle) shb) shb) (lin_one hu1))
    calc ‖k‖ + (i + cχ + cw + σb + 2) + (cw + σb) + σb + 1 = (‖k‖ + cχ + cw + σb + 2 + cw + σb + σb + 1) + i := by ring
      _ ≤ ((2 * fχ + 3 * Cb + 33 : ℕ) : V) * (‖k‖ + 1) + i := add_le_add hsum (le_refl i)
  have cap5 : (Cs : V) * (‖k‖ + (i + cχ + cw + σb + 2) + (cw + σb) + σb + 1) ≤ E := by
    refine cap_master (A := Cs * (2 * fχ + 3 * Cb + 33)) ?_ hE ?_
    · rw [hCχ, hA]
      calc Cs * (2 * fχ + 3 * Cb + 33) ≤ (Cs + 1) * (40 * (fχ + Cn + Cb + qχ + 1)) := Nat.mul_le_mul (by omega) (by omega)
        _ = 40 * (fχ + Cn + Cb + qχ + 1) * (Cs + 1) := Nat.mul_comm _ _
    · calc (Cs : V) * (‖k‖ + (i + cχ + cw + σb + 2) + (cw + σb) + σb + 1)
          ≤ (Cs : V) * (((2 * fχ + 3 * Cb + 33 : ℕ) : V) * (‖k‖ + 1) + i) := mul_le_mul_of_nonneg_left hin (by simp)
        _ = ((Cs * (2 * fχ + 3 * Cb + 33) : ℕ) : V) * (‖k‖ + 1) + (Cs : V) * i := by push_cast; ring
        _ ≤ ((Cs * (2 * fχ + 3 * Cb + 33) : ℕ) : V) * (‖k‖ + 1) + ((Cs * (2 * fχ + 3 * Cb + 33) : ℕ) : V) * i :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_mul_of_pos_right Cs (by omega)) (by simp))
  obtain ⟨Ps, oks, nds, shs, hsub⟩ := hS hΓ₄ hDχ₄ hDx₄ hDw₄ cap5
  set σs := shiftsV Ps with hσs
  set Γ₅ := finalCtx Γ₄ Ps with hΓ₅def
  have hΓ₅ : IsFormulaSet LAct Γ₅ := finalCtx_isFormulaSet 9 htbl hΓ₄ oks
  have hy₅ := transport_eq nds hy₄
  have hb₅ := transport_bnum nds hbf₄
  have ha₅ := transport_adj nds ha₄
  -- ===== block 6: the kernel
  set x := i + cχ + cw + σb + 2 + σs with hxdef
  have hCχ1 : 1 ≤ Cχ := by omega
  have hcapx : x + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : cχ + cw + σb + 2 + σs + 1 ≤ ((2 * fχ + 14 + Cb + 2 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) :=
      lin_add (lin_add (lin_add (lin_add (lin_add hcχle hcwle) shb) (lin_two hu1)) shs) (lin_one hu1)
    calc x + 1 = (cχ + cw + σb + 2 + σs + 1) + i := by rw [hxdef]; ring
      _ ≤ ((2 * fχ + 14 + Cb + 2 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) + i := add_le_add hsum (le_refl i)
      _ ≤ (Cχ : V) * (‖k‖ + 1) + i := add_le_add (lin_mono (by omega) (le_refl _)) (le_refl i)
  have hcapy : cw + σb + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : cw + σb + σs + 1 ≤ ((14 + Cb + Cs + 1 : ℕ) : V) * (‖k‖ + 1) :=
      lin_add (lin_add (lin_add hcwle shb) shs) (lin_one hu1)
    exact le_trans (lin_mono (by omega) hsum) le_self_add
  have hcapv : σb + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : σb + σs + 1 ≤ ((Cb + Cs + 1 : ℕ) : V) * (‖k‖ + 1) := lin_add (lin_add shb shs) (lin_one hu1)
    exact le_trans (lin_mono (by omega) hsum) le_self_add
  have hcapt : 1 + σb + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : 1 + σb + σs + 1 ≤ ((1 + Cb + Cs + 1 : ℕ) : V) * (‖k‖ + 1) :=
      lin_add (lin_add (lin_add (lin_one hu1) shb) shs) (lin_one hu1)
    exact le_trans (lin_mono (by omega) hsum) le_self_add
  have hcapc : 2 * (⌜χ⌝ : V) + 1 ≤ E := by
    rw [← hqV]
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc 2 * ((qχ : ℕ) : V) + 1 = ((2 * qχ + 1 : ℕ) : V) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (lin_const hu1)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  have hcapk : termLen LAct (bnum k) ≤ E := by
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc termLen LAct (bnum k) ≤ 6 * ‖k‖ + 1 := hlenk
      _ ≤ 6 * ‖k‖ + 6 := add_le_add (le_refl _) (by norm_num)
      _ = ((6 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (le_refl _)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  obtain ⟨kok, knd, ksh, _, _, hK⟩ := pinKernel_ok (x := x) (y := cw + σb + σs) (v := σb + σs) (t := 1 + σb + σs)
    (c := (⌜χ⌝ : V)) (k := k) htbl hT rfl hΓ₅ hcapx hcapy hcapv hcapt hcapc hcapk hsub hy₅ hb₅ ha₅
  set K := pinKernelSteps numIdPieces x (cw + σb + σs) (σb + σs) (1 + σb + σs) (⌜χ⌝ : V) k with hKdef
  -- ===== the assembly
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : 8 ≤ 9)
  refine ⟨appendV S₁ (appendV S₂ (appendV Pb (appendV Pn (appendV Ps K)))), ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV (ok₁.mono h89) (listOK_appendV (ok₂.mono h89) (listOK_appendV okb
      (listOK_appendV hPn.1 (listOK_appendV oks kok))))
  · exact noDrop'_appendV nd₁.noDrop' (noDrop'_appendV nd₂.noDrop' (noDrop'_appendV ndb
      (noDrop'_appendV hPn.2.1 (noDrop'_appendV nds knd))))
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, sh₁, sh₂, hPn.2.2.1, ksh]
    have hsum : cχ + (cw + (σb + (0 + (σs + 0)))) ≤ ((2 * fχ + (14 + (Cb + Cs)) : ℕ) : V) * (‖k‖ + 1) := by
      rw [zero_add, add_zero]
      exact lin_add hcχle (lin_add hcwle (lin_add shb shs))
    exact lin_mono (by omega) hsum
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV,
      shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, sh₁, sh₂, hPn.2.2.1, ksh]
    have e : i + 2 + (cχ + (cw + (σb + (0 + (σs + 0))))) = x := by rw [hxdef]; ring
    rw [e]
    exact hK

end assembly

/-! ## 3. Status (2026-09-15)

**Delivered.** `NumIdTable` (the pin's rows in the table), the kernel `pinKernel_ok`, and the assembly
`pin_assembly`: `PinKit.pin` minus its cost conjunct, modulo the two oracles.

**`PinKit.pin` still needs** (each is exactly one oracle):

1. `BnumOracle tbl E k Cb` — a `Σ₁` producer `bnumSteps k j` over the bits of `k` on the TERM dossier of
   `bnum k` (DESIGN §7.1 step 1): per bit one `sLemma` `𝟏 ≤ bnum m` (`NumSteps.oneLe_proof`) and one Horn
   step `bnumEvenCert`/`bnumOddOfEven` (both now in the table at cap `9`, `NumIdRows.lean`) reading the
   dossier's `funcFact`/`adjFact`s; the two occurrences of `𝟏` inside `𝟐 = 𝟏 ^+ 𝟏` are different
   eigenvariables and must first be identified (`eqOfFunc` at `𝟎`, then `congAdj`). A PR/`Fixpoint`
   construction with its `_ok` by binary induction — the `NumSteps`/`Cert` Part-5 template.
2. `SubstOracle tbl E χ k Cs` — `Cert.certSubst_ok` (re-indexed by `Prologue.reidxL`) at
   `w = bnum k ∷ 0`, `r = ⌜χ⌝`, `m = 0`, `n = 1`: its `SubFPre E Q …` needs `Q ≥ listSum (termLenVec …
   (qVecIterV w e))` for every `e ≤ |χ|`, i.e. bounds on the iterated `qVec` of the vector (`3e + |bnum k|`),
   and the `qWalkP` length bound `L`; both are elementary but not written. NOTE its shift count
   `2·Q·|χ|` with `Q ≥ |bnum k| ≈ 6‖k‖` is `O(‖k‖)` (fits `shiftsV ≤ Cs·(‖k‖+1)`), but its LENGTH bound
   `sfK L Q · |χ|` is QUADRATIC in `‖k‖`.

**`PinKit.cost` cannot be discharged from the generic cost lemmas** (`Frag1.costSum_le_of_sizeOK`,
`Cert.costSum_certSubst_le`): they charge the context growth at `4·B·E` per step (`ctxAfter_len_le`), so a
list of `L` steps costs `≳ L²·B·E`; with `L = Θ(‖k‖)` this is `‖k‖²·E`, while the kit allows only
`Cχ·(‖k‖+1)·E` — for the same reason `VerifyKit.cost` needs more than the generic accounting. The stated
bound IS plausible for the pin (the added facts have size `O(i + ‖k‖)`, not `B·E`, and `setLen Γ ≥ ‖k‖·i`
since `Γ` holds the dossier of `instB ⌜χ⌝ k`), but that is a finer cost analysis (actual witness sizes,
and a lower bound on `setLen Γ` from `RootLayout`) that no existing lemma provides. Either the kit's cost
conjunct is weakened at the top (`Top.lean`, e.g. to `Cχ·(‖k‖+1)²·(setLen Γ + N + E + (‖k‖+1)²)`, which
`top_main`'s cubic budget may or may not absorb — `E` itself is `Θ(‖k‖)` there) or the finer analysis is
written. Nothing here is an axiom; the two oracles are hypotheses of `pin_assembly`.
-/

end ArithS

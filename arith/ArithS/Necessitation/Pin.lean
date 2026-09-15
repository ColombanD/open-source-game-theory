import ArithS.Necessitation.NumIdRows
import ArithS.Necessitation.NumId
import ArithS.Necessitation.BnumSteps

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

/-! ## 4. The binary-numeral oracle, discharged (`BnumSteps.lean`) -/

section bnumOracle

lemma NumIdTable.bnRows {tbl : V} (h : NumIdTable tbl) : BnRows tbl :=
  ⟨h.bnumZeroCert, h.bnumOneCert, h.bnumEvenCert, h.bnumOddOfEven⟩

/-- **`BnumOracle` holds with the standard constant `27`**: the list `bnumSteps numIdPieces walkPieces tblN k j`
(`NumTableOK tblN N' B'` for the `sLemma`s `𝟏 ≤ bnum m`). -/
theorem bnumOracle_of {tbl N tblN N' B' E k : V} (htbl : TableOK tbl N) (hT : NumIdTable tbl)
    (htblN : NumTableOK tblN N' B') : BnumOracle tbl E k 27 := by
  intro Γ j hΓ hD hE
  have hE' : j + 27 * (‖k‖ + 1) ≤ E := by
    refine le_trans ?_ hE
    push_cast
    calc j + 27 * (‖k‖ + 1) ≤ 27 * j + 27 * (‖k‖ + 1) :=
          add_le_add (le_mul_of_one_le_left zero_le (by norm_num)) le_rfl
      _ = 27 * (‖k‖ + j + 1) := by ring
  obtain ⟨ok, nd, sh, _, _, hf⟩ := bnumSteps_ok htbl hT.layoutTable hT.bnRows htblN hΓ hD hE'
  refine ⟨_, ok, nd, by rw [sh]; exact zero_le, ?_⟩
  rw [sh, add_zero]; exact hf

end bnumOracle

/-! ## 5. The substitution oracle, discharged (`Cert.certSubst_ok` re-indexed)

`Cert.len_subFGraph_le` bounds the length of the formula pass by `sfK L Q · |r|` with `sfK L Q = L + 12Q(Q + 1) +
12(Q + 1) + 10` — QUADRATIC in the sum bound `Q`, hence quadratic in `‖k‖` for the vector `bnum k ∷ 0`. The
square is an artifact: in the quantifier case the mode-`1` vector pass is bounded by `len_subVGraph_le'` whose
entry-length parameter `S` is vacuous at mode `1` (`μ = 0 → …`) and was instantiated at `S := Q`. Instantiating
it at `S := 0` gives the LINEAR `sfL L Q = L + 24Q + 22` (`len_subFGraph_le_lin`, the same induction) — which
is what makes `len Ps ≤ Cs·(‖k‖ + 1)` and hence the coarse cost conjunct of `PinKit'` reachable. -/

section substOracle

noncomputable def sfL (L Q : V) : V := L + 24 * Q + 22

lemma one_le_sfL (L Q : V) : (1 : V) ≤ sfL L Q := by
  unfold sfL; exact le_trans (by norm_num) le_add_self

set_option maxHeartbeats 4000000 in
/-- **Length bound, linear in `Q`** (`Cert.len_subFGraph_le` with the mode-`1` vector pass bounded at `S := 0`). -/
lemma len_subFGraph_le_lin (W Wd : V) {n₀ m₀ w₀ : V} (hw₀ : IsSemitermVec LAct n₀ m₀ w₀) (D L Q : V)
    (hQ : ∀ e ≤ D, listSum (termLenVec LAct (n₀ + e) (qVecIterV LAct w₀ e)) ≤ Q)
    (hL : ∀ e ≤ D, len (π₂ (qWalkP Wd (m₀ + e) (n₀ + e) (qVecIterV LAct w₀ e))) ≤ L) :
    ∀ {n r : V}, IsSemiformula LAct n r →
    ∀ d, d + formulaLen LAct r ≤ D → n = n₀ + d → ∀ i j iw y : V,
      SubFGraph W Wd n (m₀ + d) (qVecIterV LAct w₀ d) iw r i j y → len y ≤ sfL L Q * formulaLen LAct r := by
  intro n r
  apply IsSemiformula.pi1_structural_induction
    (P := fun n r ↦ ∀ d, d + formulaLen LAct r ≤ D → n = n₀ + d → ∀ i j iw y : V,
      SubFGraph W Wd n (m₀ + d) (qVecIterV LAct w₀ d) iw r i j y → len y ≤ sfL L Q * formulaLen LAct r)
  · simp only [SubFGraph]; definability
  · intro n k R v hkR hv d hD hn i j iw y hy
    subst hn
    have hwd := isSemitermVec_qVecIterV hw₀ d
    rw [formulaLen_rel hkR hv.isUTerm] at hD
    rw [SubFGraph.rel_iff.mp hy, len_sfAtomSteps, formulaLen_rel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hl := len_subVGraph_le' W iw 0 (fun _ ↦ hwd) (listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)))
      (fun _ z hz ↦ termLen_nth_le_listSum hwd hz) hv k le_rfl (i + 1) (j + 1) _ (subV_graph (fun _ ↦ hwd) hv le_rfl)
    rw [htl] at hl
    have hQd : listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) ≤ Q :=
      hQ d (le_trans le_self_add (le_trans (add_le_add (le_refl d) (le_add_self)) hD))
    calc len (subV W (qVecIterV LAct w₀ d) iw (m₀ + d) 0 (n₀ + d) k v k (i + 1) (j + 1)) + 2
        ≤ 12 * listSum (termLenVec LAct k v) * (listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) + 1) + 4 := hl
      _ ≤ 12 * listSum (termLenVec LAct k v) * (Q + 1) + 4 :=
          add_le_add (mul_le_mul_of_nonneg_left (add_le_add hQd (le_refl 1)) zero_le) (le_refl 4)
      _ ≤ listSum (termLenVec LAct k v) * sfL L Q + sfL L Q := by
          refine add_le_add ?_ ?_
          · rw [mul_comm (12 * listSum (termLenVec LAct k v)), ← mul_assoc, mul_comm (Q + 1) 12, mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            unfold sfL
            calc 12 * (Q + 1) ≤ 12 * (Q + 1) + (L + 12 * Q + 10) := le_self_add
              _ = L + 24 * Q + 22 := by ring
          · unfold sfL
            calc (4 : V) ≤ 22 := by norm_num
              _ ≤ L + 24 * Q + 22 := le_add_self
      _ = sfL L Q * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n k R v hkR hv d hD hn i j iw y hy
    subst hn
    have hwd := isSemitermVec_qVecIterV hw₀ d
    rw [formulaLen_nrel hkR hv.isUTerm] at hD
    rw [SubFGraph.nrel_iff.mp hy, len_sfAtomSteps, formulaLen_nrel hkR hv.isUTerm]
    have htl : takeLast v k = v := by rw [← hv.lh]; exact takeLast_len_self v
    have hl := len_subVGraph_le' W iw 0 (fun _ ↦ hwd) (listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)))
      (fun _ z hz ↦ termLen_nth_le_listSum hwd hz) hv k le_rfl (i + 1) (j + 1) _ (subV_graph (fun _ ↦ hwd) hv le_rfl)
    rw [htl] at hl
    have hQd : listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) ≤ Q :=
      hQ d (le_trans le_self_add (le_trans (add_le_add (le_refl d) (le_add_self)) hD))
    calc len (subV W (qVecIterV LAct w₀ d) iw (m₀ + d) 0 (n₀ + d) k v k (i + 1) (j + 1)) + 2
        ≤ 12 * listSum (termLenVec LAct k v) * (listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) + 1) + 4 := hl
      _ ≤ 12 * listSum (termLenVec LAct k v) * (Q + 1) + 4 :=
          add_le_add (mul_le_mul_of_nonneg_left (add_le_add hQd (le_refl 1)) zero_le) (le_refl 4)
      _ ≤ listSum (termLenVec LAct k v) * sfL L Q + sfL L Q := by
          refine add_le_add ?_ ?_
          · rw [mul_comm (12 * listSum (termLenVec LAct k v)), ← mul_assoc, mul_comm (Q + 1) 12, mul_comm]
            refine mul_le_mul_of_nonneg_left ?_ zero_le
            unfold sfL
            calc 12 * (Q + 1) ≤ 12 * (Q + 1) + (L + 12 * Q + 10) := le_self_add
              _ = L + 24 * Q + 22 := by ring
          · unfold sfL
            calc (4 : V) ≤ 22 := by norm_num
              _ ≤ L + 24 * Q + 22 := le_add_self
      _ = sfL L Q * (listSum (termLenVec LAct k v) + 1) := by ring
  · intro n d _ _ i j iw y hy
    rw [SubFGraph.verum_iff.mp hy, len_sfConstSteps, formulaLen_verum, mul_one]; exact one_le_sfL L Q
  · intro n d _ _ i j iw y hy
    rw [SubFGraph.falsum_iff.mp hy, len_sfConstSteps, formulaLen_falsum, mul_one]; exact one_le_sfL L Q
  · intro n p q hp hq ihp ihq d hD hn i j iw y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := SubFGraph.and_iff.mp hy
    rw [formulaLen_and hp.isUFormula hq.isUFormula] at hD ⊢
    have hDq : d + formulaLen LAct q ≤ D :=
      le_trans (add_le_add (le_refl d) (le_trans le_add_self le_self_add)) hD
    have hDp : d + formulaLen LAct p ≤ D :=
      le_trans (add_le_add (le_refl d) (le_trans le_self_add le_self_add)) hD
    rw [len_sfBinSteps]
    calc len yq + (len yp + 1) ≤ sfL L Q * formulaLen LAct q + (sfL L Q * formulaLen LAct p + sfL L Q) :=
          add_le_add (ihq d hDq hn _ _ _ _ hyq) (add_le_add (ihp d hDp hn _ _ _ _ hyp) (one_le_sfL L Q))
      _ = sfL L Q * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p q hp hq ihp ihq d hD hn i j iw y hy
    obtain ⟨yq, yp, _, _, hyq, hyp, rfl⟩ := SubFGraph.or_iff.mp hy
    rw [formulaLen_or hp.isUFormula hq.isUFormula] at hD ⊢
    have hDq : d + formulaLen LAct q ≤ D :=
      le_trans (add_le_add (le_refl d) (le_trans le_add_self le_self_add)) hD
    have hDp : d + formulaLen LAct p ≤ D :=
      le_trans (add_le_add (le_refl d) (le_trans le_self_add le_self_add)) hD
    rw [len_sfBinSteps]
    calc len yq + (len yp + 1) ≤ sfL L Q * formulaLen LAct q + (sfL L Q * formulaLen LAct p + sfL L Q) :=
          add_le_add (ihq d hDq hn _ _ _ _ hyq) (add_le_add (ihp d hDp hn _ _ _ _ hyp) (one_le_sfL L Q))
      _ = sfL L Q * (formulaLen LAct p + formulaLen LAct q + 1) := by ring
  · intro n p hp ih d hD hn i j iw y hy
    subst hn
    obtain ⟨yb, _, hyb, rfl⟩ := SubFGraph.all_iff.mp hy
    rw [formulaLen_all hp.isUFormula] at hD ⊢
    have hwd := isSemitermVec_qVecIterV hw₀ d
    have hDp : d + 1 + formulaLen LAct p ≤ D := by rw [add_assoc, add_comm 1]; exact hD
    have hLd : len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) ≤ L :=
      hL d (le_trans le_self_add (le_trans (add_le_add (le_refl d) le_add_self) hD))
    have hQd : listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) ≤ Q :=
      hQ d (le_trans le_self_add (le_trans (add_le_add (le_refl d) le_add_self) hD))
    have hb : len yb ≤ sfL L Q * formulaLen LAct p := by
      have := ih (d + 1) hDp (by ring) _ _ _ _ (by rw [qVecIterV_succ, show m₀ + (d + 1) = m₀ + d + 1 by ring]; exact hyb)
      exact this
    have htl : takeLast (qVecIterV LAct w₀ d) (n₀ + d) = qVecIterV LAct w₀ d := by
      have := takeLast_len_self (qVecIterV LAct w₀ d); rwa [hwd.lh] at this
    have hLb := len_subVGraph_le' W (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 1 (n := m₀ + d) (m := m₀ + d)
      (w := qVecIterV LAct w₀ d) (fun h ↦ absurd h _root_.one_ne_zero) 0 (fun h ↦ absurd h _root_.one_ne_zero) hwd (n₀ + d) le_rfl
      (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2 _
      (subV_graph (W := W) (w := qVecIterV LAct w₀ d) (m := m₀ + d) (fun h ↦ absurd h _root_.one_ne_zero) hwd le_rfl)
    rw [htl] at hLb
    have hLb' : len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
        (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + 2
        ≤ 12 * Q * (0 + 1) + 4 :=
      le_trans hLb (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQd zero_le) zero_le) (le_refl 4))
    rw [len_sfQuantSteps]
    calc len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) +
          (len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
            (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + (3 + (len yb + 1)))
        = (len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) +
            (len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
              (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + 2) + 2) + len yb := by ring
      _ ≤ (L + (12 * Q * (0 + 1) + 4) + 2) + sfL L Q * formulaLen LAct p := add_le_add (add_le_add (add_le_add hLd hLb') (le_refl 2)) hb
      _ ≤ sfL L Q + sfL L Q * formulaLen LAct p := by
          refine add_le_add ?_ (le_refl _)
          unfold sfL
          calc L + (12 * Q * (0 + 1) + 4) + 2 = L + 12 * Q + 6 := by ring
            _ ≤ L + 12 * Q + 6 + (12 * Q + 16) := le_self_add
            _ = L + 24 * Q + 22 := by ring
      _ = sfL L Q * (formulaLen LAct p + 1) := by ring
  · intro n p hp ih d hD hn i j iw y hy
    subst hn
    obtain ⟨yb, _, hyb, rfl⟩ := SubFGraph.exs_iff.mp hy
    rw [formulaLen_exs hp.isUFormula] at hD ⊢
    have hwd := isSemitermVec_qVecIterV hw₀ d
    have hDp : d + 1 + formulaLen LAct p ≤ D := by rw [add_assoc, add_comm 1]; exact hD
    have hLd : len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) ≤ L :=
      hL d (le_trans le_self_add (le_trans (add_le_add (le_refl d) le_add_self) hD))
    have hQd : listSum (termLenVec LAct (n₀ + d) (qVecIterV LAct w₀ d)) ≤ Q :=
      hQ d (le_trans le_self_add (le_trans (add_le_add (le_refl d) le_add_self) hD))
    have hb : len yb ≤ sfL L Q * formulaLen LAct p := by
      have := ih (d + 1) hDp (by ring) _ _ _ _ (by rw [qVecIterV_succ, show m₀ + (d + 1) = m₀ + d + 1 by ring]; exact hyb)
      exact this
    have htl : takeLast (qVecIterV LAct w₀ d) (n₀ + d) = qVecIterV LAct w₀ d := by
      have := takeLast_len_self (qVecIterV LAct w₀ d); rwa [hwd.lh] at this
    have hLb := len_subVGraph_le' W (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 1 (n := m₀ + d) (m := m₀ + d)
      (w := qVecIterV LAct w₀ d) (fun h ↦ absurd h _root_.one_ne_zero) 0 (fun h ↦ absurd h _root_.one_ne_zero) hwd (n₀ + d) le_rfl
      (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2 _
      (subV_graph (W := W) (w := qVecIterV LAct w₀ d) (m := m₀ + d) (fun h ↦ absurd h _root_.one_ne_zero) hwd le_rfl)
    rw [htl] at hLb
    have hLb' : len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
        (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + 2
        ≤ 12 * Q * (0 + 1) + 4 :=
      le_trans hLb (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQd zero_le) zero_le) (le_refl 4))
    rw [len_sfQuantSteps]
    calc len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) +
          (len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
            (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + (3 + (len yb + 1)))
        = (len (π₂ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) +
            (len (subV W (qVecIterV LAct w₀ d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) (m₀ + d) 1 (m₀ + d)
              (n₀ + d) (qVecIterV LAct w₀ d) (n₀ + d) (iw + π₁ (qWalkP Wd (m₀ + d) (n₀ + d) (qVecIterV LAct w₀ d))) 2) + 2) + 2) + len yb := by ring
      _ ≤ (L + (12 * Q * (0 + 1) + 4) + 2) + sfL L Q * formulaLen LAct p := add_le_add (add_le_add (add_le_add hLd hLb') (le_refl 2)) hb
      _ ≤ sfL L Q + sfL L Q * formulaLen LAct p := by
          refine add_le_add ?_ (le_refl _)
          unfold sfL
          calc L + (12 * Q * (0 + 1) + 4) + 2 = L + 12 * Q + 6 := by ring
            _ ≤ L + 12 * Q + 6 + (12 * Q + 16) := le_self_add
            _ = L + 24 * Q + 22 := by ring
      _ = sfL L Q * (formulaLen LAct p + 1) := by ring

/-- The linear length bound of `certSubst` itself. -/
lemma len_certSubst_le_lin {Wd W n m w iw r i j Q L : V} (hw : IsSemitermVec LAct n m w) (hr : IsSemiformula LAct n r)
    (hQ : ∀ e ≤ formulaLen LAct r, listSum (termLenVec LAct (n + e) (qVecIterV LAct w e)) ≤ Q)
    (hL : ∀ e ≤ formulaLen LAct r, len (π₂ (qWalkP Wd (m + e) (n + e) (qVecIterV LAct w e))) ≤ L) :
    len (certSubst W Wd n m w iw r i j) ≤ sfL L Q * formulaLen LAct r :=
  len_subFGraph_le_lin W Wd hw (formulaLen LAct r) L Q hQ hL hr 0 (by rw [zero_add]) (by rw [add_zero]) i j iw
    (certSubst W Wd n m w iw r i j) (by rw [add_zero, qVecIterV_zero]; exact certSubst_graph hw hr)

/-- The cap helper: `z ≤ A·(‖k‖ + 1) + t` with `t ≤ x + y + iw` and `A ≤ Cs` gives `z ≤ E`. -/
lemma capS {A Cs : ℕ} {k x y iw E z t : V} (hA1 : 1 ≤ Cs) (hA : A ≤ Cs) (hE : (Cs : V) * (‖k‖ + x + y + iw + 1) ≤ E)
    (ht : t ≤ x + y + iw) (hz : z ≤ (A : V) * (‖k‖ + 1) + t) : z ≤ E := by
  refine le_trans hz (le_trans ?_ hE)
  calc (A : V) * (‖k‖ + 1) + t ≤ (Cs : V) * (‖k‖ + 1) + (Cs : V) * (x + y + iw) :=
        add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hA) zero_le)
          (le_trans ht (le_mul_of_one_le_left zero_le (by exact_mod_cast hA1)))
    _ = (Cs : V) * (‖k‖ + x + y + iw + 1) := by ring

set_option maxHeartbeats 2000000 in
/-- **The certified substitution of `bnum k` into `χ`, re-indexed to the pin table**: from the three dossiers
(source `⌜χ⌝` at `&y`, image `instB ⌜χ⌝ k` at `&x`, vector `bnum k ∷ 0` at `&iw`) a Horn-only, cut-admitting list
at cap `9` with shifts AND length `≤ Cs·(‖k‖ + 1)` (`Cs` standard, per `χ`) leaving `substFact &(x+σ) &(iw+σ) &(y+σ)`. -/
theorem substSteps_ok (χ : Semisentence LAct 1) :
    ∃ Cs : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E Γ y x iw k : V},
      TableOK tbl N → ProTable tbl → IsFormulaSet LAct Γ → DossF walkPieces Γ 1 (⌜χ⌝ : V) y →
      DossF walkPieces Γ 0 (instB (⌜χ⌝ : V) k) x → DossV walkPieces Γ 0 1 (bnum k ∷ 0) 1 iw →
      (Cs : V) * (‖k‖ + x + y + iw + 1) ≤ E →
      ∃ Ps : V, ListOK tbl E ((9 : ℕ) : V) Γ Ps ∧ NoDrop' Ps ∧ HornOnly Ps ∧ shiftsV Ps ≤ (Cs : V) * (‖k‖ + 1) ∧
        len Ps ≤ (Cs : V) * (‖k‖ + 1) ∧
        neg LAct (substFact (^&(x + shiftsV Ps)) (^&(iw + shiftsV Ps)) (^&(y + shiftsV Ps))) ∈ finalCtx Γ Ps := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ, f = flN (⌜χ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = (1 + f) * (f + 7) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℕ, l = 12 * ((f + 2) * (f + 8)) + 2 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A : ℕ, A = 4 * f + 2 * q + 11 := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A : ℕ, A = 2 * f * (q + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A : ℕ, A = 12 * f + 2 * q * f + 1 := ⟨_, rfl⟩
  obtain ⟨A₄, hA₄⟩ : ∃ A : ℕ, A = 2 * q * (f + 1) + 2 := ⟨_, rfl⟩
  obtain ⟨A₅, hA₅⟩ : ∃ A : ℕ, A = 2 * q * f := ⟨_, rfl⟩
  obtain ⟨A₆, hA₆⟩ : ∃ A : ℕ, A = (l + 24 * q + 22) * f := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ C : ℕ, C = A₁ + A₂ + A₃ + A₄ + A₅ + A₆ + 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ Cs := by omega
  refine ⟨Cs, fun V _ _ tbl N E Γ y x iw k htbl hP hΓ hDy hDx hDw hE ↦ ?_⟩
  -- the source as a variable, its standard length
  obtain ⟨c, hc⟩ : ∃ c : V, c = ⌜χ⌝ := ⟨_, rfl⟩
  have hr : IsSemiformula LAct (1 : V) c := by rw [hc]; exact Sentence.quote_isSemiformul₁ χ
  have hfV : formulaLen LAct c = (f : V) := by
    rw [hc, hf, ← Sentence.coe_quote_eq_quote (V := V) χ, flN_cast]
  rw [← hc] at hDy hDx
  have hDx' : DossF walkPieces Γ 0 (subst LAct (bnum k ∷ 0) c) x := hDx
  -- the vector
  have hbk : IsSemiterm LAct 0 (bnum k) := isSemiterm_bnum_LAct 0 k
  have hw : IsSemitermVec LAct 1 0 (bnum k ∷ (0 : V)) := by simp [hbk]
  have hB : termLen LAct (bnum k) ≤ 6 * ‖k‖ + 1 := termLen_bnum_le_bk le_rfl
  have hu1 : (1 : V) ≤ ‖k‖ + 1 := le_add_self
  have hB6 : 6 * ‖k‖ + 1 ≤ ((6 : ℕ) : V) * (‖k‖ + 1) := by
    push_cast; rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num)
  -- Q and L
  obtain ⟨Q, hQ⟩ : ∃ Q : V, Q = (1 + formulaLen LAct c) * (1 + formulaLen LAct c + (6 * ‖k‖ + 1)) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : V, L = 12 * ((1 + formulaLen LAct c + 1) * (1 + formulaLen LAct c + 1 + (6 * ‖k‖ + 1))) + 2 := ⟨_, rfl⟩
  have hQle : Q ≤ (q : V) * (‖k‖ + 1) := by
    rw [hQ, hfV, hq]; push_cast
    have h1 : 1 + (f : V) + (6 * ‖k‖ + 1) ≤ ((f : V) + 7) * (‖k‖ + 1) := by
      calc 1 + (f : V) + (6 * ‖k‖ + 1) ≤ (1 + (f : V)) * (‖k‖ + 1) + 6 * (‖k‖ + 1) :=
            add_le_add (le_mul_of_one_le_right zero_le hu1) (by rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num))
        _ = ((f : V) + 7) * (‖k‖ + 1) := by ring
    calc (1 + (f : V)) * (1 + (f : V) + (6 * ‖k‖ + 1)) ≤ (1 + (f : V)) * (((f : V) + 7) * (‖k‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1 zero_le
      _ = (1 + (f : V)) * ((f : V) + 7) * (‖k‖ + 1) := by ring
  have hLle : L ≤ (l : V) * (‖k‖ + 1) := by
    rw [hL, hfV, hl]; push_cast
    have h1 : 1 + (f : V) + 1 + (6 * ‖k‖ + 1) ≤ ((f : V) + 8) * (‖k‖ + 1) := by
      calc 1 + (f : V) + 1 + (6 * ‖k‖ + 1) ≤ (1 + (f : V) + 1) * (‖k‖ + 1) + 6 * (‖k‖ + 1) :=
            add_le_add (le_mul_of_one_le_right zero_le hu1) (by rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num))
        _ = ((f : V) + 8) * (‖k‖ + 1) := by ring
    calc 12 * ((1 + (f : V) + 1) * (1 + (f : V) + 1 + (6 * ‖k‖ + 1))) + 2
        ≤ 12 * ((1 + (f : V) + 1) * (((f : V) + 8) * (‖k‖ + 1))) + 2 * (‖k‖ + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 zero_le) zero_le) (le_mul_of_one_le_right zero_le hu1)
      _ = (12 * (((f : V) + 2) * ((f : V) + 8)) + 2) * (‖k‖ + 1) := by ring
  have hfu : formulaLen LAct c ≤ (f : V) * (‖k‖ + 1) := by rw [hfV]; exact le_mul_of_one_le_right zero_le hu1
  -- the four caps of `subFPre_single`
  have cap1 : 4 * formulaLen LAct c + 2 * Q + 11 ≤ E := by
    refine capS hC1 (by omega : A₁ ≤ Cs) hE (t := 0) zero_le ?_
    rw [add_zero, hA₁]; push_cast
    calc 4 * formulaLen LAct c + 2 * Q + 11 ≤ 4 * ((f : V) * (‖k‖ + 1)) + 2 * ((q : V) * (‖k‖ + 1)) + 11 * (‖k‖ + 1) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfu zero_le) (mul_le_mul_of_nonneg_left hQle zero_le))
            (le_mul_of_one_le_right zero_le hu1)
      _ = (4 * (f : V) + 2 * (q : V) + 11) * (‖k‖ + 1) := by ring
  have cap2 : y + 2 * formulaLen LAct c * (Q + 1) + 1 ≤ E := by
    refine capS hC1 (by omega : A₂ ≤ Cs) hE (t := y) (le_trans le_add_self le_self_add) ?_
    rw [hA₂]; push_cast
    have hQ1 : Q + 1 ≤ ((q : V) + 1) * (‖k‖ + 1) := by
      calc Q + 1 ≤ (q : V) * (‖k‖ + 1) + (‖k‖ + 1) := add_le_add hQle hu1
        _ = ((q : V) + 1) * (‖k‖ + 1) := by ring
    calc y + 2 * formulaLen LAct c * (Q + 1) + 1
        ≤ y + 2 * (f : V) * (((q : V) + 1) * (‖k‖ + 1)) + 1 * (‖k‖ + 1) := by
          rw [hfV]
          exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hQ1 zero_le)) (le_mul_of_one_le_right zero_le hu1)
      _ = (2 * (f : V) * ((q : V) + 1) + 1) * (‖k‖ + 1) + y := by ring
  have hsub : formulaLen LAct (subst LAct (bnum k ∷ 0) c) ≤ formulaLen LAct c * (6 * ‖k‖ + 1) :=
    formulaLen_subst_le (L := LAct) (le_trans (by norm_num) le_add_self) hr 0 _ hw (substInv_single hbk hB)
  have cap3 : x + 2 * formulaLen LAct (subst LAct (bnum k ∷ 0) c) + 2 * Q * formulaLen LAct c + 1 ≤ E := by
    refine capS hC1 (by omega : A₃ ≤ Cs) hE (t := x) (le_trans le_self_add le_self_add) ?_
    rw [hA₃]; push_cast
    have h1 : 2 * formulaLen LAct (subst LAct (bnum k ∷ 0) c) ≤ 12 * (f : V) * (‖k‖ + 1) := by
      calc 2 * formulaLen LAct (subst LAct (bnum k ∷ 0) c) ≤ 2 * (formulaLen LAct c * (6 * ‖k‖ + 1)) :=
            mul_le_mul_of_nonneg_left hsub zero_le
        _ ≤ 2 * ((f : V) * (((6 : ℕ) : V) * (‖k‖ + 1))) := by
            rw [hfV]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB6 zero_le) zero_le
        _ = 12 * (f : V) * (‖k‖ + 1) := by push_cast; ring
    have h2 : 2 * Q * formulaLen LAct c ≤ 2 * (q : V) * (f : V) * (‖k‖ + 1) := by
      rw [hfV]
      calc 2 * Q * (f : V) ≤ 2 * ((q : V) * (‖k‖ + 1)) * (f : V) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle zero_le) zero_le
        _ = 2 * (q : V) * (f : V) * (‖k‖ + 1) := by ring
    calc x + 2 * formulaLen LAct (subst LAct (bnum k ∷ 0) c) + 2 * Q * formulaLen LAct c + 1
        ≤ x + 12 * (f : V) * (‖k‖ + 1) + 2 * (q : V) * (f : V) * (‖k‖ + 1) + 1 * (‖k‖ + 1) :=
          add_le_add (add_le_add (add_le_add le_rfl h1) h2) (le_mul_of_one_le_right zero_le hu1)
      _ = (12 * (f : V) + 2 * (q : V) * (f : V) + 1) * (‖k‖ + 1) + x := by ring
  have cap4 : iw + 2 * Q * (formulaLen LAct c + 1) + 2 ≤ E := by
    refine capS hC1 (by omega : A₄ ≤ Cs) hE (t := iw) le_add_self ?_
    rw [hA₄, hfV]; push_cast
    calc iw + 2 * Q * ((f : V) + 1) + 2 ≤ iw + 2 * ((q : V) * (‖k‖ + 1)) * ((f : V) + 1) + 2 * (‖k‖ + 1) :=
          add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle zero_le) zero_le))
            (le_mul_of_one_le_right zero_le hu1)
      _ = (2 * (q : V) * ((f : V) + 1) + 2) * (‖k‖ + 1) + iw := by ring
  have hPre : SubFPre E Q 1 0 (bnum k ∷ 0) c y x iw Γ := by
    rw [hQ]; exact subFPre_single hbk hB (by rw [← hQ]; exact cap1) (by rw [← hQ]; exact cap2) (by rw [← hQ]; exact cap3)
      (by rw [← hQ]; exact cap4) hΓ
  have hLc : ∀ e ≤ formulaLen LAct c, len (π₂ (qWalkP walkPieces (0 + e) (1 + e) (qVecIterV LAct (bnum k ∷ 0) e))) ≤ L := by
    rw [hL]; exact qWalkP_single_cap hbk hB
  -- the certification at the view, re-indexed
  have htblV : TableOK (certView tbl) N := hP.tableOK_certView htbl
  have hC : CertTable (certView tbl) := hP.certTable
  obtain ⟨ok, nd, hho, hsh, _, hfact⟩ := certSubst_ok htblV hC rfl rfl hw hr hPre hLc hDy hDx' hDw
  have hlen := len_certSubst_le_lin (Wd := walkPieces) (W := certPieces) (iw := iw) (i := y) (j := x) hw hr hPre.2.1 hLc
  refine ⟨reidxL (certSubst certPieces walkPieces 1 0 (bnum k ∷ 0) iw c y x), listOK_reidxL hP ok, noDrop'_reidxL nd,
    hornOnly_reidxL hho, ?_, ?_, ?_⟩
  · rw [shiftsV_reidxL]
    refine le_trans hsh ?_
    refine lin_mono (by omega : A₅ ≤ Cs) ?_
    rw [hA₅, hfV]; push_cast
    calc 2 * Q * (f : V) ≤ 2 * ((q : V) * (‖k‖ + 1)) * (f : V) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle zero_le) zero_le
      _ = 2 * (q : V) * (f : V) * (‖k‖ + 1) := by ring
  · rw [len_reidxL]
    refine le_trans hlen ?_
    refine lin_mono (by omega : A₆ ≤ Cs) ?_
    rw [hA₆, hfV]; push_cast
    unfold sfL
    calc (L + 24 * Q + 22) * (f : V) ≤ ((l : V) * (‖k‖ + 1) + 24 * ((q : V) * (‖k‖ + 1)) + 22 * (‖k‖ + 1)) * (f : V) :=
          mul_le_mul_of_nonneg_right (add_le_add (add_le_add hLle (mul_le_mul_of_nonneg_left hQle zero_le))
            (le_mul_of_one_le_right zero_le hu1)) zero_le
      _ = ((l : V) + 24 * (q : V) + 22) * (f : V) * (‖k‖ + 1) := by ring
  · rw [finalCtx_reidxL, shiftsV_reidxL]
    rw [vRef_of_ne _root_.one_ne_zero] at hfact
    exact hfact

/-- **`SubstOracle` holds** with the constant of `substSteps_ok`. -/
theorem substOracle_of (χ : Semisentence LAct 1) :
    ∃ Cs : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N E k : V},
      TableOK tbl N → ProTable tbl → SubstOracle tbl E χ k Cs := by
  obtain ⟨Cs, h⟩ := substSteps_ok χ
  refine ⟨Cs, fun V _ _ tbl N E k htbl hP Γ y x iw hΓ hDy hDx hDw hE ↦ ?_⟩
  obtain ⟨Ps, ok, nd, _, hsh, _, hf⟩ := h V htbl hP hΓ hDy hDx hDw hE
  exact ⟨Ps, ok, nd, hsh, hf⟩

end substOracle

/-! ## 6. The pin with its length and size discipline; the three cost conjuncts; `PinKit'`

The cost is taken in ONE shot: `Frag1.costSum_le_of_sizeOK` over the whole assembled list (every block is
`SizeOK` — the walks and `certSubst` are Horn-only, `NumId` is `SizeOK Cn Cn`, the kernel `SizeOK 0 0`, and
`bnumSteps` is `SizeOK (bQ B' ‖k‖) (bD N' B' ‖k‖)`), at `Q := Cχ·(‖k‖ + 1) ≤ kitQ Cχ B E` and `D := Cχ·(‖k‖ + 1)³ =
kitD Cχ ‖k‖`, with `len P ≤ Cχ·(‖k‖ + 1)`; the end-context bounds are `ctxVec_len_le_sizeOK` at `len P`. This
is equivalent to (and shorter than) summing the per-block cost lemmas through `costSum_appendV`. -/

section pinFull

lemma costK_mono {N E B M Q Q' D D' : V} (hQ : Q ≤ Q') (hD : D ≤ D') : costK N E B M Q D ≤ costK N E B M Q' D' := by
  unfold costK
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ zero_le) zero_le)) le_rfl)
    (mul_le_mul_of_nonneg_left hQ zero_le)) hD) le_rfl

lemma growK_mono {B E Q Q' : V} (hQ : Q ≤ Q') : growK B E Q ≤ growK B E Q' := by
  unfold growK; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hQ zero_le)

lemma ctxBoundG_mono2 {G G' Γ L L' : V} (hG : G ≤ G') (hL : L ≤ L') : ctxBoundG G Γ L ≤ ctxBoundG G' Γ L' := by
  unfold ctxBoundG
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hL zero_le))
    (mul_le_mul (add_le_add (mul_le_mul hL hL zero_le zero_le) hL) hG zero_le zero_le)

set_option maxHeartbeats 4000000 in
/-- **The pin, fully produced** (`pin_assembly` with the two oracles DISCHARGED — `bnumSteps` and the re-indexed
`certSubst` — and the length and size discipline tracked): for an explicit standard `Cχ` (depending on `χ` and the
`NumSteps` bounds `N' B'`), from the root layout of `instB ⌜χ⌝ k` at `&i`, a list `P` applicable at cap `9`,
cut-admitting, `shiftsV P ≤ Cχ·(‖k‖+1)`, leaving `instBFact &(i + 2 + shiftsV P) (qNum χ) (bnum k)`, with
`len P ≤ Cχ·(‖k‖+1)` and `SizeOK (Cχ·(‖k‖+1)) (Cχ·(‖k‖+1)³) P`. -/
theorem pin_full (χ : Semisentence LAct 1) (N' B' : ℕ) :
    ∃ Cχ : ℕ, 1 ≤ Cχ ∧ ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N tblN E Γ i k : V},
      TableOK tbl N → NumIdTable tbl → NumTableOK tblN (N' : V) (B' : V) → IsFormulaSet LAct Γ →
      RootLayout Γ (instB (⌜χ⌝ : V) k) i → (Cχ : V) * (‖k‖ + i + 1) ≤ E →
      ∃ P : V, ListOK tbl E ((9 : ℕ) : V) Γ P ∧ NoDrop' P ∧ shiftsV P ≤ (Cχ : V) * (‖k‖ + 1) ∧
        neg LAct (instBFact (^&(i + 2 + shiftsV P)) (qNum χ) (bnum k)) ∈ finalCtx Γ P ∧
        len P ≤ (Cχ : V) * (‖k‖ + 1) ∧ SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) P := by
  obtain ⟨Cn, hCn⟩ := numId_sentence χ
  obtain ⟨Cs, hCs⟩ := substSteps_ok χ
  obtain ⟨fχ, hfχ⟩ : ∃ f : ℕ, f = flN (⌜χ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨qχ, hqχ⟩ : ∃ q : ℕ, q = (⌜χ⌝ : ℕ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ, A = 40 * (fχ + Cn + 27 + qχ + 1) := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℕ, C = A * (Cs + 1) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = 12 * fχ + 100 + Cn + Cs + 6 * B' + 5 * (N' + 9600 * B') := ⟨_, rfl⟩
  obtain ⟨Cχ, hCχ⟩ : ∃ C : ℕ, C = C₀ + R := ⟨_, rfl⟩
  refine ⟨Cχ, by omega, ?_⟩
  intro V _ _ tbl N tblN E Γ i k htbl hT htblN hΓ hR hE
  have hW : WalkTable tbl := hT.walkTable
  have hu1 : (1 : V) ≤ ‖k‖ + 1 := le_add_self
  -- the standard quantities of χ in V
  have hfV : formulaLen LAct (⌜χ⌝ : V) = (fχ : V) := by
    rw [hfχ, ← Sentence.coe_quote_eq_quote (V := V) χ, flN_cast]
  have hqV : ((qχ : ℕ) : V) = ⌜χ⌝ := by rw [hqχ]; exact Sentence.coe_quote_eq_quote χ
  have hr : IsSemiformula LAct (1 : V) (⌜χ⌝ : V) := Sentence.quote_isSemiformul₁ χ
  have hlenk : termLen LAct (bnum k) ≤ 6 * ‖k‖ + 1 := termLen_bnum_le_bk le_rfl
  have hC₀C : C₀ ≤ Cχ := by rw [hCχ]; exact Nat.le_add_right _ _
  have hRC : R ≤ Cχ := by rw [hCχ]; exact Nat.le_add_left _ _
  have hAC₀ : A ≤ C₀ := by rw [hC₀]; exact Nat.le_mul_of_pos_right A (by omega)
  have hAC : A ≤ Cχ := le_trans hAC₀ hC₀C
  have hACs : A + Cs ≤ Cχ := by
    refine le_trans ?_ hC₀C
    rw [hC₀]
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
  have hl₁ := len_describeF_le walkPieces hr
  set S₁ := describeF walkPieces 1 (⌜χ⌝ : V) with hS₁
  set cχ := descCountF walkPieces 1 (⌜χ⌝ : V) with hcχ
  set Γ₁ := finalCtx Γ S₁ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ ok₁
  have hcχle : cχ ≤ (2 * fχ : ℕ) * (‖k‖ + 1) := by
    have : cχ + 1 ≤ 2 * (fχ : V) := by rw [← hfV]; exact cnt₁
    push_cast
    exact le_trans (le_trans le_self_add this) (le_mul_of_one_le_right (by simp) hu1)
  have hlen₁ : len S₁ ≤ ((12 * fχ : ℕ) : V) * (‖k‖ + 1) := by
    have : len S₁ ≤ 12 * (fχ : V) := by rw [← hfV]; exact le_trans le_self_add hl₁
    push_cast
    exact le_trans this (le_mul_of_one_le_right zero_le hu1)
  have hsz₁ : SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) S₁ := sizeOK_of_hornOnly (hornOnly_describeF rfl hr)
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
  have htl : takeLast w 1 = w := by have := takeLast_len_self w; rwa [hlw] at this
  have hcwle : cw ≤ ((14 : ℕ) : V) * (‖k‖ + 1) := by
    have h2 := hcnt₂
    rw [htl, hlenw] at h2
    calc cw ≤ 2 * termLen LAct (bnum k) := h2
      _ ≤ 2 * (6 * ‖k‖ + 1) := mul_le_mul_of_nonneg_left hlenk (by simp)
      _ = 12 * ‖k‖ + 2 := by ring
      _ ≤ 14 * ‖k‖ + 14 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) (by simp)) (by norm_num)
      _ = ((14 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
  have hlen₂ : len S₂ ≤ ((86 : ℕ) : V) * (‖k‖ + 1) := by
    obtain ⟨_, hl⟩ := len_descVecAux_le hw' (fun i hi ↦ len_describeT_le walkPieces 0 _ (hw'.nth hi)) 1 le_rfl
    rw [htl, hlenw] at hl
    calc len S₂ ≤ 12 * termLen LAct (bnum k) + 4 := le_trans le_self_add (le_trans hl (le_of_eq (by ring)))
      _ ≤ 12 * (6 * ‖k‖ + 1) + 4 := add_le_add (mul_le_mul_of_nonneg_left hlenk zero_le) le_rfl
      _ = 72 * ‖k‖ + 16 := by ring
      _ ≤ 86 * ‖k‖ + 86 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ = ((86 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
  have hsz₂ : SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) S₂ :=
    sizeOK_of_hornOnly (hornOnly_descVecAux rfl hw' (fun i hi ↦ hornOnly_describeT rfl 0 _ (hw'.nth hi)) 1 le_rfl)
  have hDw₂ : DossV walkPieces Γ₂ 0 1 w 1 0 := dossV_of_walk nd₂
  have hDχ₂ : DossF walkPieces Γ₂ 1 (⌜χ⌝ : V) cw := by
    have := dossF_transport' nd₂.noDrop' hDχ₁; rwa [sh₂, zero_add] at this
  have hR₂ : RootLayout Γ₂ (instB (⌜χ⌝ : V) k) (i + cχ + cw) := by
    have := hR₁.transport nd₂.noDrop'; rwa [sh₂] at this
  have hDw₂' : DossV walkPieces Γ₂ 0 1 w ((0 : V) + 1) 0 := by rw [zero_add]; exact hDw₂
  obtain ⟨ha₂, _, hDt₂, _⟩ := dossV_succ htbl hW rfl hw' (by rw [zero_add]) hDw₂'
  have e10 : (1 : V) - ((0 : V) + 1) = 0 := by rw [zero_add]; exact tsub_eq_zero_of_le (le_refl _)
  rw [e10, hwdef, nth_adjoin_zero, zero_add] at hDt₂
  rw [vRef_zero, zero_add] at ha₂
  -- ===== block 3: the binary numeral certification (bnumSteps)
  have cap3 : (1 : V) + 27 * (‖k‖ + 1) ≤ E := by
    refine cap_master (A := 28) (by omega) hE ?_
    calc (1 : V) + 27 * (‖k‖ + 1) ≤ 1 * (‖k‖ + 1) + 27 * (‖k‖ + 1) :=
          add_le_add (le_mul_of_one_le_right zero_le hu1) le_rfl
      _ = ((28 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ ((28 : ℕ) : V) * (‖k‖ + 1) + ((28 : ℕ) : V) * i := le_self_add
  obtain ⟨okb, ndb, shb, hlenb, hszb, hbf⟩ := bnumSteps_ok htbl hT.layoutTable hT.bnRows htblN hΓ₂ hDt₂ cap3
  set Pb := bnumSteps numIdPieces walkPieces tblN k 1 with hPbdef
  set Γ₃ := finalCtx Γ₂ Pb with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 9 htbl hΓ₂ okb
  have hbf₃ : neg LAct (bnumFact (^&1) (bnum k)) ∈ Γ₃ := hbf
  have ha₃ : neg LAct (adjFact (^&0) (^&1) (𝟎 : V)) ∈ Γ₃ := by
    have := transport_adj ndb ha₂; rwa [shb, add_zero, add_zero] at this
  have hDχ₃ : DossF walkPieces Γ₃ 1 (⌜χ⌝ : V) cw := by
    have := dossF_transport' ndb hDχ₂; rwa [shb, add_zero] at this
  have hDw₃ : DossV walkPieces Γ₂ 0 1 w 1 0 → DossV walkPieces Γ₃ 0 1 w 1 0 := fun h ↦ by
    have := dossV_transport' ndb h; rwa [shb, add_zero] at this
  have hDw₃' := hDw₃ hDw₂
  have hR₃ : RootLayout Γ₃ (instB (⌜χ⌝ : V) k) (i + cχ + cw) := by
    have := hR₂.transport ndb; rwa [shb, add_zero] at this
  have hlenb' : len Pb ≤ ((9 : ℕ) : V) * (‖k‖ + 1) := by
    refine le_trans hlenb ?_
    push_cast
    calc 8 * ‖k‖ + 1 ≤ 9 * ‖k‖ + 9 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) (by norm_num)
      _ = 9 * (‖k‖ + 1) := by ring
  -- the size discipline of Pb at the kit's parameters
  have hu3 : (‖k‖ + 1) ≤ (‖k‖ + 1) ^ 3 := by
    rw [show (‖k‖ + 1) ^ 3 = (‖k‖ + 1) * ((‖k‖ + 1) * (‖k‖ + 1)) by ring]
    exact le_mul_of_one_le_right zero_le (one_le_mul_of_one_le_of_one_le hu1 hu1)
  have hu23 : (‖k‖ + 1) * (‖k‖ + 1) ≤ (‖k‖ + 1) ^ 3 := by
    rw [show (‖k‖ + 1) ^ 3 = (‖k‖ + 1) * (‖k‖ + 1) * (‖k‖ + 1) by ring]
    exact le_mul_of_one_le_right zero_le hu1
  have hQb : bQ (B' : V) ‖k‖ ≤ (Cχ : V) * (‖k‖ + 1) := by
    unfold bQ
    calc (B' : V) * (6 * ‖k‖ + 1) ≤ (B' : V) * (6 * (‖k‖ + 1)) :=
          mul_le_mul_of_nonneg_left (by rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num)) zero_le
      _ = ((6 * B' : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ (Cχ : V) * (‖k‖ + 1) := lin_mono (by omega) le_rfl
  have hDb : bD (N' : V) (B' : V) ‖k‖ ≤ (Cχ : V) * (‖k‖ + 1) ^ 3 := by
    unfold bD nodeCost
    have hnc : (N' : V) + 800 * ((B' : V) * (12 * ‖k‖ + 3)) ≤ ((N' + 9600 * B' : ℕ) : V) * (‖k‖ + 1) := by
      push_cast
      calc (N' : V) + 800 * ((B' : V) * (12 * ‖k‖ + 3)) ≤ (N' : V) * (‖k‖ + 1) + 800 * ((B' : V) * (12 * (‖k‖ + 1))) :=
            add_le_add (le_mul_of_one_le_right zero_le hu1) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (by rw [mul_add, mul_one]; exact add_le_add le_rfl (by norm_num)) zero_le) zero_le)
        _ = ((N' : V) + 9600 * (B' : V)) * (‖k‖ + 1) := by ring
    have hk2 : ‖k‖ + 2 ≤ 2 * (‖k‖ + 1) := by
      rw [mul_add, mul_one]
      calc ‖k‖ + 2 ≤ ‖k‖ + ‖k‖ + 2 := add_le_add le_self_add le_rfl
        _ = 2 * ‖k‖ + 2 := by ring
    calc (1 + 1) * (‖k‖ + 2) * ((N' : V) + 800 * ((B' : V) * (12 * ‖k‖ + 3))) + ((N' : V) + 800 * ((B' : V) * (12 * ‖k‖ + 3)))
        ≤ (1 + 1) * (2 * (‖k‖ + 1)) * (((N' + 9600 * B' : ℕ) : V) * (‖k‖ + 1)) + ((N' + 9600 * B' : ℕ) : V) * (‖k‖ + 1) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hk2 zero_le) hnc zero_le zero_le) hnc
      _ = ((N' + 9600 * B' : ℕ) : V) * (4 * ((‖k‖ + 1) * (‖k‖ + 1)) + (‖k‖ + 1)) := by ring
      _ ≤ ((N' + 9600 * B' : ℕ) : V) * (4 * (‖k‖ + 1) ^ 3 + (‖k‖ + 1) ^ 3) :=
          mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hu23 zero_le) hu3) zero_le
      _ = ((5 * (N' + 9600 * B') : ℕ) : V) * (‖k‖ + 1) ^ 3 := by push_cast; ring
      _ ≤ (Cχ : V) * (‖k‖ + 1) ^ 3 := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 5 * (N' + 9600 * B') ≤ Cχ)) zero_le
  have hszb' : SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) Pb := hszb.mono hQb hDb
  -- ===== block 4: the numeral identification of χ (NumId)
  have cap4 : (Cn : V) + cw ≤ E := by
    refine cap_master' (A := A) (by omega) hAC hE ?_
    calc (Cn : V) + cw ≤ (Cn : V) * (‖k‖ + 1) + ((14 : ℕ) : V) * (‖k‖ + 1) := add_le_add (lin_const hu1) hcwle
      _ = ((Cn + 14 : ℕ) : V) * (‖k‖ + 1) := by push_cast; ring
      _ ≤ (A : V) * (‖k‖ + 1) := lin_mono (by omega) (le_refl _)
      _ ≤ (A : V) * (‖k‖ + 1) + i := le_self_add
  obtain ⟨Pn, hPn⟩ := hCn V htbl hT.layoutTable hΓ₃ (by rw [Nat.cast_one]; exact hDχ₃) cap4
  set Γ₄ := finalCtx Γ₃ Pn with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := hPn.isFormulaSet htbl hΓ₃
  have hy₄ : neg LAct (eqFact (^&cw) (numeral (⌜χ⌝ : V))) ∈ Γ₄ := hPn.2.2.2.2.2
  have hbf₄ := hPn.mem hbf₃
  have ha₄ := hPn.mem ha₃
  have hDχ₄ : DossF walkPieces Γ₄ 1 (⌜χ⌝ : V) cw := hPn.dossF hDχ₃
  have hDw₄ : DossV walkPieces Γ₄ 0 1 w 1 0 := hPn.dossV hDw₃'
  have hR₄ : RootLayout Γ₄ (instB (⌜χ⌝ : V) k) (i + cχ + cw) := by
    have := hR₃.transport hPn.2.1; rwa [hPn.2.2.1, add_zero] at this
  have hDx₄ : DossF walkPieces Γ₄ 0 (instB (⌜χ⌝ : V) k) (i + cχ + cw + 2) := hR₄.1
  have hlenn : len Pn ≤ (Cn : V) * (‖k‖ + 1) := le_trans hPn.2.2.2.1 (lin_const hu1)
  have hszn : SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) Pn :=
    hPn.2.2.2.2.1.mono (lin_mono (by omega) (lin_const hu1)) (le_trans (lin_mono (by omega) (lin_const hu1))
      (mul_le_mul_of_nonneg_left hu3 zero_le))
  -- ===== block 5: the certified substitution (substSteps)
  have hin : ‖k‖ + (i + cχ + cw + 2) + cw + 0 + 1 ≤ ((2 * fχ + 32 : ℕ) : V) * (‖k‖ + 1) + i := by
    have h1 : ‖k‖ ≤ ((1 : ℕ) : V) * (‖k‖ + 1) := by push_cast; rw [one_mul]; exact le_self_add
    have hsum : ‖k‖ + cχ + cw + 2 + cw + 1 ≤ ((2 * fχ + 32 : ℕ) : V) * (‖k‖ + 1) :=
      lin_mono (by omega) (lin_add (lin_add (lin_add (lin_add (lin_add h1 hcχle) hcwle) (lin_two hu1)) hcwle) (lin_one hu1))
    calc ‖k‖ + (i + cχ + cw + 2) + cw + 0 + 1 = (‖k‖ + cχ + cw + 2 + cw + 1) + i := by ring
      _ ≤ ((2 * fχ + 32 : ℕ) : V) * (‖k‖ + 1) + i := add_le_add hsum (le_refl i)
  have cap5 : (Cs : V) * (‖k‖ + (i + cχ + cw + 2) + cw + 0 + 1) ≤ E := by
    refine cap_master (A := Cs * (2 * fχ + 32)) ?_ hE ?_
    · refine le_trans ?_ hC₀C
      rw [hC₀, hA]
      calc Cs * (2 * fχ + 32) ≤ (Cs + 1) * (40 * (fχ + Cn + 27 + qχ + 1)) := Nat.mul_le_mul (by omega) (by omega)
        _ = 40 * (fχ + Cn + 27 + qχ + 1) * (Cs + 1) := Nat.mul_comm _ _
    · calc (Cs : V) * (‖k‖ + (i + cχ + cw + 2) + cw + 0 + 1)
          ≤ (Cs : V) * (((2 * fχ + 32 : ℕ) : V) * (‖k‖ + 1) + i) := mul_le_mul_of_nonneg_left hin (by simp)
        _ = ((Cs * (2 * fχ + 32) : ℕ) : V) * (‖k‖ + 1) + (Cs : V) * i := by push_cast; ring
        _ ≤ ((Cs * (2 * fχ + 32) : ℕ) : V) * (‖k‖ + 1) + ((Cs * (2 * fχ + 32) : ℕ) : V) * i :=
          add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_mul_of_pos_right Cs (by omega)) (by simp))
  obtain ⟨Ps, oks, nds, hhos, shs, hlens, hsub⟩ := hCs V htbl hT.proTable hΓ₄ hDχ₄ hDx₄ hDw₄ cap5
  set σs := shiftsV Ps with hσs
  set Γ₅ := finalCtx Γ₄ Ps with hΓ₅def
  have hΓ₅ : IsFormulaSet LAct Γ₅ := finalCtx_isFormulaSet 9 htbl hΓ₄ oks
  have hy₅ := transport_eq nds hy₄
  have hb₅ := transport_bnum nds hbf₄
  have ha₅ := transport_adj nds ha₄
  have hszs : SizeOK ((Cχ : V) * (‖k‖ + 1)) ((Cχ : V) * (‖k‖ + 1) ^ 3) Ps := sizeOK_of_hornOnly hhos
  -- ===== block 6: the kernel
  set x := i + cχ + cw + 2 + σs with hxdef
  have hCχ1 : 1 ≤ Cχ := by omega
  have hcapx : x + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : cχ + cw + 2 + σs + 1 ≤ ((2 * fχ + 14 + 2 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) :=
      lin_add (lin_add (lin_add (lin_add hcχle hcwle) (lin_two hu1)) shs) (lin_one hu1)
    calc x + 1 = (cχ + cw + 2 + σs + 1) + i := by rw [hxdef]; ring
      _ ≤ ((2 * fχ + 14 + 2 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) + i := add_le_add hsum (le_refl i)
      _ ≤ (Cχ : V) * (‖k‖ + 1) + i := add_le_add (lin_mono (by omega) (le_refl _)) (le_refl i)
  have hcapy : cw + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : cw + σs + 1 ≤ ((14 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) := lin_add (lin_add hcwle shs) (lin_one hu1)
    exact le_trans (lin_mono (by omega) hsum) le_self_add
  have hcapv : 0 + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : 0 + σs + 1 ≤ ((Cs + 1 : ℕ) : V) * (‖k‖ + 1) := by
      rw [zero_add]; exact lin_add shs (lin_one hu1)
    exact le_trans (lin_mono (by omega) hsum) le_self_add
  have hcapt : 1 + σs + 1 ≤ E := by
    refine cap_master' (A := Cχ) hCχ1 le_rfl hE ?_
    have hsum : 1 + σs + 1 ≤ ((1 + Cs + 1 : ℕ) : V) * (‖k‖ + 1) := lin_add (lin_add (lin_one hu1) shs) (lin_one hu1)
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
  obtain ⟨kok, knd, ksh, klen, ksz, hK⟩ := pinKernel_ok (x := x) (y := cw + σs) (v := 0 + σs) (t := 1 + σs)
    (c := (⌜χ⌝ : V)) (k := k) htbl hT rfl hΓ₅ hcapx hcapy hcapv hcapt hcapc hcapk hsub hy₅ hb₅ ha₅
  set K := pinKernelSteps numIdPieces x (cw + σs) (0 + σs) (1 + σs) (⌜χ⌝ : V) k with hKdef
  -- ===== the assembly
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : 8 ≤ 9)
  refine ⟨appendV S₁ (appendV S₂ (appendV Pb (appendV Pn (appendV Ps K)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact listOK_appendV (ok₁.mono h89) (listOK_appendV (ok₂.mono h89) (listOK_appendV okb
      (listOK_appendV hPn.1 (listOK_appendV oks kok))))
  · exact noDrop'_appendV nd₁.noDrop' (noDrop'_appendV nd₂.noDrop' (noDrop'_appendV ndb
      (noDrop'_appendV hPn.2.1 (noDrop'_appendV nds knd))))
  · rw [shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, sh₁, sh₂, shb, hPn.2.2.1, ksh]
    have hsum : cχ + (cw + (0 + (0 + (σs + 0)))) ≤ ((2 * fχ + (14 + Cs) : ℕ) : V) * (‖k‖ + 1) := by
      rw [zero_add, zero_add, add_zero]
      exact lin_add hcχle (lin_add hcwle shs)
    exact lin_mono (by omega) hsum
  · rw [finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV,
      shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, shiftsV_appendV, sh₁, sh₂, shb, hPn.2.2.1, ksh]
    have e : i + 2 + (cχ + (cw + (0 + (0 + (σs + 0))))) = x := by rw [hxdef]; ring
    rw [e]
    exact hK
  · rw [len_appendV, len_appendV, len_appendV, len_appendV, len_appendV, klen]
    have hsum : len S₁ + (len S₂ + (len Pb + (len Pn + (len Ps + 2)))) ≤
        ((12 * fχ + (86 + (9 + (Cn + (Cs + 2)))) : ℕ) : V) * (‖k‖ + 1) :=
      lin_add hlen₁ (lin_add hlen₂ (lin_add hlenb' (lin_add hlenn (lin_add hlens (lin_two hu1)))))
    exact lin_mono (by omega) hsum
  · exact sizeOK_appendV hsz₁ (sizeOK_appendV hsz₂ (sizeOK_appendV hszb' (sizeOK_appendV hszn
      (sizeOK_appendV hszs (ksz.mono zero_le zero_le)))))

/-- **`PinKit'` holds**, for every `χ`, with the constant of `pin_full` (per `χ` and the `NumSteps` bounds), on
any pin table with row-body bound `B`: the four fact conjuncts are `pin_full`'s, the three cost conjuncts are
`Frag1.costSum_le_of_sizeOK`/`ctxVec_len_le_sizeOK` over the whole list at `Q = Cχ·(‖k‖+1) ≤ kitQ Cχ B E`,
`D = kitD Cχ ‖k‖`, `len P ≤ Cχ·(‖k‖+1)`. -/
theorem pinKit'_of (χ : Semisentence LAct 1) (N' B' : ℕ) :
    ∃ Cχ : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {tbl N B tblN : V},
      TableOK tbl N → NumIdTable tbl → (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) →
      NumTableOK tblN (N' : V) (B' : V) → PinKit' χ tbl N B Cχ := by
  obtain ⟨Cχ, hCχ1, h⟩ := pin_full χ N' B'
  refine ⟨Cχ, fun V _ _ tbl N B tblN htbl hT hBt htblN ↦ ⟨fun k Γ i E hR hΓ hE ↦ ?_⟩⟩
  obtain ⟨P, ok, nd, sh, hf, hlen, hsz⟩ := h V htbl hT htblN hΓ hR hE
  have hu1 : (1 : V) ≤ ‖k‖ + 1 := le_add_self
  have hkE : ‖k‖ + 1 ≤ E := by
    refine le_trans ?_ hE
    calc ‖k‖ + 1 ≤ ‖k‖ + i + 1 := add_le_add le_self_add le_rfl
      _ ≤ (Cχ : V) * (‖k‖ + i + 1) := le_mul_of_one_le_left zero_le (by exact_mod_cast hCχ1)
  have hE1 : (1 : V) ≤ E := le_trans hu1 hkE
  have hQk : (Cχ : V) * (‖k‖ + 1) ≤ kitQ (Cχ : V) B E := by
    unfold kitQ
    refine mul_le_mul_of_nonneg_left (le_trans hkE ?_) zero_le
    calc E ≤ E + 1 := le_self_add
      _ ≤ (B + 1) * (E + 1) := le_mul_of_one_le_left zero_le le_add_self
  have hDk : (Cχ : V) * (‖k‖ + 1) ^ 3 ≤ kitD (Cχ : V) ‖k‖ := le_of_eq rfl
  have hG : growK B E ((Cχ : V) * (‖k‖ + 1)) ≤ growK B E (kitQ (Cχ : V) B E) := growK_mono hQk
  have cost := costSum_le_of_sizeOK 9 hE1 htbl hBt ok hsz
  obtain ⟨hF, hS⟩ := ctxVec_len_le_sizeOK 9 hE1 htbl hBt ok hsz (len P) le_rfl
  have h38 : (3 * ((9 : ℕ) : V) + 11) = 38 := by push_cast; norm_num
  refine ⟨P, ok, nd, sh, hf, ?_, ?_, ?_⟩
  · refine le_trans cost ?_
    rw [h38]
    refine mul_le_mul hlen ?_ zero_le zero_le
    refine add_le_add (costK_mono hQk hDk) (mul_le_mul_of_nonneg_left ?_ zero_le)
    exact add_le_add (ctxBoundG_mono2 hG hlen) (add_le_add le_rfl (mul_le_mul hlen hG zero_le zero_le))
  · show setLen LAct (ctxVec Γ P).[len P] ≤ _
    exact le_trans hS (ctxBoundG_mono2 hG hlen)
  · show fvOccS LAct (ctxVec Γ P).[len P] ≤ _
    exact le_trans hF (add_le_add le_rfl (mul_le_mul hlen hG zero_le zero_le))

end pinFull

/-! ## 7. The package: one table per model, the row-body bound, `PinKit'` for every `χ` -/

section package

/-- The row-body bound of a `WRow` list: the sum of the standard lengths of its matrices. -/
noncomputable def rowsB : List WRow → ℕ
  | [] => 0
  | r :: rs => flN (⌜Semiformula.lMap emb r.B⌝ : ℕ) + rowsB rs

lemma flN_le_rowsB : ∀ (rs : List WRow) (i : ℕ) (h : i < rs.length),
    flN (⌜Semiformula.lMap emb (rs[i]).B⌝ : ℕ) ≤ rowsB rs
  | [], i, h => absurd h (Nat.not_lt_zero _)
  | r :: rs, 0, _ => by simp only [List.getElem_cons_zero, rowsB]; exact Nat.le_add_right _ _
  | r :: rs, i + 1, h => by
    simp only [List.getElem_cons_succ, rowsB]
    exact le_trans (flN_le_rowsB rs i (Nat.lt_of_succ_lt_succ h)) (Nat.le_add_left _ _)

/-- **A pin table with its row-body bound exists in every model** (`exists_numIdTable` with `B := rowsB numIdRows`). -/
theorem exists_numIdTableB : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ NumIdTable tbl ∧ ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ (B : V) := by
  obtain ⟨N, hN⟩ := exists_rows numIdRows
  refine ⟨N, rowsB numIdRows, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ⟨?_, ?_⟩, ?_⟩
  · rw [len_vecOf, hlen, numIdRows_length]
  · intro i h
    have h' : i < rows.length := by rw [hlen]; exact h
    rw [nth_vecOf rows i h']
    exact hidx i h h'
  · intro j hj
    rw [len_vecOf] at hj
    obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hj
    have h' : i < rows.length := by exact_mod_cast hj
    have h : i < numIdRows.length := by rw [← hlen]; exact h'
    rw [nth_vecOf rows i h', (hidx i h h').2, ← Sentence.coe_quote_eq_quote (V := V), flN_cast]
    exact_mod_cast flN_le_rowsB numIdRows i h

/-- **The pin half of `KitPackage'`**: standard `N B N' B'` and a per-`χ` constant `Cχ` such that every model has
a pin table (`NumIdTable ⇒ ProTable ⇒ TopTable`) with row-body bound `B`, a `NumSteps` table, and `PinKit' χ tbl
N B (Cχ χ)` for EVERY `χ`. -/
theorem pinKit'_package : ∃ (N B N' B' : ℕ) (Cχ : Semisentence LAct 1 → ℕ),
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁], ∃ tbl tblN : V,
      TableOK tbl (N : V) ∧ NumIdTable tbl ∧ (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ (B : V)) ∧
      NumTableOK tblN (N' : V) (B' : V) ∧ ∀ χ : Semisentence LAct 1, PinKit' χ tbl (N : V) (B : V) (Cχ χ) := by
  obtain ⟨N', B', hNum⟩ := exists_numTable
  obtain ⟨N, B, hTab⟩ := exists_numIdTableB
  refine ⟨N, B, N', B', fun χ ↦ Classical.choose (pinKit'_of χ N' B'), fun V _ _ ↦ ?_⟩
  obtain ⟨tbl, htbl, hT, hB⟩ := hTab V
  obtain ⟨tblN, hN⟩ := hNum V
  exact ⟨tbl, tblN, htbl, hT, hB, hN, fun χ ↦ Classical.choose_spec (pinKit'_of χ N' B') V htbl hT hB hN⟩

end package

end ArithS

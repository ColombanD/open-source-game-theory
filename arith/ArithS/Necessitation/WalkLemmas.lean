import ArithS.Necessitation.Steps
import ArithS.Necessitation.ShiftLen
import ArithS.Necessitation.Lib.Walk

/-!
# ArithS.Necessitation.WalkLemmas — V-lemmas for the formula walk

`M4_BOUNDED_HBL/DESIGN_describe.md` §10, the V-generic side (any model of `𝗜𝚺₁`, three
standard axioms):

1. **The chain numeral `cT`** (§1.4): `cTV : V → V`, `cTV 0 = 𝟎`, `cTV (n + 1) = cTV n ^+ 𝟏`
   (Σ₁ by primitive recursion, so it exists at NONSTANDARD `n` — the bound-variable index `z`
   of a nonstandard formula, §3.3); `cT n := cTV (n : ℕ)`; the meta term `cTT : ℕ →
   ClosedSemiterm ℒₒᵣ 0` (`0`, `0 + 1`, …) with `quote_cTT : ⌜cTT n⌝ = cT n`, so a row written
   with the literal `0 + 1 + 1` instantiates to `cT 2` (`cTT_two`, and the closed symbol rows
   of `Lib/Walk.lean` are `⇜ ![cTT k, cTT R]` by `rfl`). Laws: `IsSemiterm ℒₒᵣ/LAct k (cTV n)`,
   `termLen (cTV n) = 2n + 1`, `termShift (cTV n) = cTV n`, `termSubst w (cTV n) = cTV n`,
   `termBShift (cTV n) = cTV n`, `fvOcc (cTV n) = 0` — at both languages where the operation is
   `L`-indexed.
2. **`bvOcc`**: bound-variable occurrence counts (`TermRec`/`UformulaRec1`, the recursion of
   `fvOcc`/`fvOccF`), invariant under `shift`, bounded by the lengths; and **the substitution
   occurrence bound** `fvOccF_subst_le : fvOccF (subst w p) ≤ fvOccF p + bvOcc p · M` whenever
   every entry of `w` has `≤ M` free-variable occurrences (the `all/exs` case goes through
   `qVec w`, whose entries are `#0` and `termBShift w.[i]` — `fvOcc_termBShift`), hence the
   sharpened `fvOccF_free_le' : fvOccF (free p) ≤ fvOccF p + bvOcc p` (`ShiftLen.lean` charged
   `formulaLen p`).
3. **Row instantiation at closed witnesses, any width** (§2.3): `instOuterAt_subst_bvList` —
   `instOuterAt k es` on `subst ?[#i₁, …, #i_N] P` is `subst ?[slot i₁, …, slot i_N] P` with
   `slot = (bvarList k ++ es.reverse).getD · 0`, for ANY index list (`Steps.lean` had `N = 2, 3`);
   `instOuter_subst_bv1/4/5/6/7` are the literal-width readings.
4. **Iterated `free`** (§2.3): `freeIter k q` — `k` eigenvariable introductions from the
   inside out (`free` of the body under `j` remaining quantifiers is `subOuter j (&0) ∘ shift`,
   `free_exsIter`); `freeIter_subst_listToVec` — `freeIter k (subst ?[#0, …, #(k-1), l] P) =
   subst ?[&0, …, &(k-1), termShift^k l] P` for closed `l` and `shift P = P`: the LAST-listed
   existential is `&0`, the outermost is `&(k-1)`, the closed witnesses shifted `k` times.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## 1. The chain numeral `cT` -/

section cT

/-! ### The codes `𝟎`, `𝟏`, `x ^+ y` under the `L`-indexed operations -/

lemma qqZero_eq : (𝟎 : V) = ^func 0 (zeroIndex : V) 0 := by
  simp [Arithmetic.zero, qqFunc_absolute, qqFuncN_eq_qqFunc]

lemma qqOne_eq : (𝟏 : V) = ^func 0 (oneIndex : V) 0 := by
  simp [Arithmetic.one, qqFunc_absolute, qqFuncN_eq_qqFunc]

lemma isFunc_LOR_zeroIndex : (ℒₒᵣ).IsFunc (0 : V) (zeroIndex : V) := by simp
lemma isFunc_LOR_oneIndex : (ℒₒᵣ).IsFunc (0 : V) (oneIndex : V) := by simp
lemma isFunc_LOR_addIndex : (ℒₒᵣ).IsFunc (2 : V) (addIndex : V) := by simp

lemma isFunc_LAct_zeroIndex : LAct.IsFunc (0 : V) (zeroIndex : V) := isFunc_LAct_of_LOR isFunc_LOR_zeroIndex
lemma isFunc_LAct_oneIndex : LAct.IsFunc (0 : V) (oneIndex : V) := isFunc_LAct_of_LOR isFunc_LOR_oneIndex
lemma isFunc_LAct_addIndex : LAct.IsFunc (2 : V) (addIndex : V) := isFunc_LAct_of_LOR isFunc_LOR_addIndex

section generic

variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma termLenVec_cons₂ {x y : V} (hx : IsUTerm L x) (hy : IsUTerm L y) :
    termLenVec L 2 (x ∷ y ∷ (0 : V)) = termLen L x ∷ termLen L y ∷ 0 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, termLenVec_cons hx (by simp [hy]),
    show (1 : V) = 0 + 1 by simp, termLenVec_cons hy (by simp), termLenVec_nil]

lemma fvOccVec_cons₂ {x y : V} (hx : IsUTerm L x) (hy : IsUTerm L y) :
    fvOccVec L 2 (x ∷ y ∷ (0 : V)) = fvOcc L x ∷ fvOcc L y ∷ 0 := by
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm, fvOccVec_cons hx (by simp [hy]),
    show (1 : V) = 0 + 1 by simp, fvOccVec_cons hy (by simp), fvOccVec_nil]

lemma termLen_qqAdd {x y : V} (ha : L.IsFunc 2 (addIndex : V)) (hx : IsUTerm L x) (hy : IsUTerm L y) :
    termLen L (x ^+ y) = termLen L x + termLen L y + 1 := by
  unfold qqAdd
  rw [termLen_func ha (by simp [hx, hy]), termLenVec_cons₂ hx hy, listSum_adjoin, listSum_adjoin,
    listSum_nil, add_zero]

lemma termLen_qqZero (hz : L.IsFunc 0 (zeroIndex : V)) : termLen L (𝟎 : V) = 1 := by
  rw [qqZero_eq, termLen_func hz (v := (0 : V)) (by simp), termLenVec_nil, listSum_nil, zero_add]

lemma termLen_qqOne (ho : L.IsFunc 0 (oneIndex : V)) : termLen L (𝟏 : V) = 1 := by
  rw [qqOne_eq, termLen_func ho (v := (0 : V)) (by simp), termLenVec_nil, listSum_nil, zero_add]

lemma termShift_qqAdd {x y : V} (ha : L.IsFunc 2 (addIndex : V)) (hx : IsUTerm L x) (hy : IsUTerm L y) :
    termShift L (x ^+ y) = termShift L x ^+ termShift L y := by
  unfold qqAdd
  rw [termShift_func ha (by simp [hx, hy]), termShiftVec_cons₂ hx hy]

lemma termShift_qqZero (hz : L.IsFunc 0 (zeroIndex : V)) : termShift L (𝟎 : V) = 𝟎 := by
  rw [qqZero_eq, termShift_func hz (v := (0 : V)) (by simp)]; simp

lemma termShift_qqOne (ho : L.IsFunc 0 (oneIndex : V)) : termShift L (𝟏 : V) = 𝟏 := by
  rw [qqOne_eq, termShift_func ho (v := (0 : V)) (by simp)]; simp

lemma fvOcc_qqAdd {x y : V} (ha : L.IsFunc 2 (addIndex : V)) (hx : IsUTerm L x) (hy : IsUTerm L y) :
    fvOcc L (x ^+ y) = fvOcc L x + fvOcc L y := by
  unfold qqAdd
  rw [fvOcc_func ha (by simp [hx, hy]), fvOccVec_cons₂ hx hy, listSum_adjoin, listSum_adjoin,
    listSum_nil, add_zero]

lemma fvOcc_qqZero (hz : L.IsFunc 0 (zeroIndex : V)) : fvOcc L (𝟎 : V) = 0 := by
  rw [qqZero_eq, fvOcc_func hz (v := (0 : V)) (by simp), fvOccVec_nil, listSum_nil]

lemma fvOcc_qqOne (ho : L.IsFunc 0 (oneIndex : V)) : fvOcc L (𝟏 : V) = 0 := by
  rw [qqOne_eq, fvOcc_func ho (v := (0 : V)) (by simp), fvOccVec_nil, listSum_nil]

end generic

/-! ### `cTV`, Σ₁ by primitive recursion -/

namespace CT

def blueprint : PR.Blueprint 0 where
  zero := .mkSigma “y. y = ↑Arithmetic.zero”
  succ := .mkSigma “y t n. !qqAddGraph y t ↑Arithmetic.one”

noncomputable def construction : PR.Construction V blueprint where
  zero := fun _ ↦ 𝟎
  succ := fun _ _ t ↦ t ^+ 𝟏
  zero_defined := .mk fun v ↦ by simp [blueprint, numeral_eq_natCast]
  succ_defined := .mk fun v ↦ by simp [qqAdd, blueprint, numeral_eq_natCast]

end CT

/-- **The chain numeral, V-generic**: `cTV 0 = 𝟎`, `cTV (n + 1) = cTV n ^+ 𝟏` — the code of
`0 + 1 + ⋯ + 1` (`n` ones), for every `n : V`. -/
noncomputable def cTV (n : V) : V := CT.construction.result ![] n

@[simp] lemma cTV_zero : cTV (0 : V) = 𝟎 := by simp [cTV, CT.construction]

@[simp] lemma cTV_succ (n : V) : cTV (n + 1) = cTV n ^+ 𝟏 := by simp [cTV, CT.construction]

def cTVGraph : 𝚺₁.Semisentence 2 := CT.blueprint.resultDef

instance cTV.defined : 𝚺₁-Function₁ (cTV : V → V) via cTVGraph := .mk fun v ↦ by
  simp [CT.construction.result_defined_iff, cTVGraph]; rfl

instance cTV.definable : 𝚺₁-Function₁ (cTV : V → V) := cTV.defined.to_definable

instance cTV.definable' : Γ-[m + 1]-Function₁ (cTV : V → V) := cTV.definable.of_sigmaOne

/-- `cTV n` is a closed `ℒₒᵣ`-term (at every bound-variable count). -/
lemma cTV_semiterm (k n : V) : IsSemiterm ℒₒᵣ k (cTV n) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [qqAdd, ih]

lemma cTV_semiterm_LAct (k n : V) : IsSemiterm LAct k (cTV n) :=
  IsSemiterm.LAct_of_LOR (cTV_semiterm k n)

lemma cTV_uterm (n : V) : IsUTerm ℒₒᵣ (cTV n) := (cTV_semiterm 0 n).isUTerm
lemma cTV_uterm_LAct (n : V) : IsUTerm LAct (cTV n) := (cTV_semiterm_LAct 0 n).isUTerm

lemma qqOne_uterm : IsUTerm ℒₒᵣ (𝟏 : V) := (one_semiterm (n := 0)).isUTerm
lemma qqOne_uterm_LAct : IsUTerm LAct (𝟏 : V) := IsUTerm.LAct_of_LOR qqOne_uterm

/-- `termLen (cTV n) = 2n + 1` (at `ℒₒᵣ`). -/
lemma termLen_cTV_LOR (n : V) : termLen ℒₒᵣ (cTV n) = 2 * n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, termLen_qqZero isFunc_LOR_zeroIndex]; simp
  case succ n ih =>
    rw [cTV_succ, termLen_qqAdd isFunc_LOR_addIndex (cTV_uterm n) qqOne_uterm, ih,
      termLen_qqOne isFunc_LOR_oneIndex]
    ring

/-- `termLen (cTV n) = 2n + 1` (at `LAct`). -/
lemma termLen_cTV (n : V) : termLen LAct (cTV n) = 2 * n + 1 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, termLen_qqZero isFunc_LAct_zeroIndex]; simp
  case succ n ih =>
    rw [cTV_succ, termLen_qqAdd isFunc_LAct_addIndex (cTV_uterm_LAct n)
      qqOne_uterm_LAct, ih, termLen_qqOne isFunc_LAct_oneIndex]
    ring

lemma termShift_cTV_LOR (n : V) : termShift ℒₒᵣ (cTV n) = cTV n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, termShift_qqZero isFunc_LOR_zeroIndex]
  case succ n ih =>
    rw [cTV_succ, termShift_qqAdd isFunc_LOR_addIndex (cTV_uterm n) qqOne_uterm, ih,
      termShift_qqOne isFunc_LOR_oneIndex]

lemma termShift_cTV (n : V) : termShift LAct (cTV n) = cTV n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, termShift_qqZero isFunc_LAct_zeroIndex]
  case succ n ih =>
    rw [cTV_succ, termShift_qqAdd isFunc_LAct_addIndex (cTV_uterm_LAct n)
      qqOne_uterm_LAct, ih, termShift_qqOne isFunc_LAct_oneIndex]

lemma fvOcc_cTV_LOR (n : V) : fvOcc ℒₒᵣ (cTV n) = 0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, fvOcc_qqZero isFunc_LOR_zeroIndex]
  case succ n ih =>
    rw [cTV_succ, fvOcc_qqAdd isFunc_LOR_addIndex (cTV_uterm n) qqOne_uterm, ih,
      fvOcc_qqOne isFunc_LOR_oneIndex, add_zero]

lemma fvOcc_cTV (n : V) : fvOcc LAct (cTV n) = 0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => rw [cTV_zero, fvOcc_qqZero isFunc_LAct_zeroIndex]
  case succ n ih =>
    rw [cTV_succ, fvOcc_qqAdd isFunc_LAct_addIndex (cTV_uterm_LAct n)
      qqOne_uterm_LAct, ih, fvOcc_qqOne isFunc_LAct_oneIndex, add_zero]

lemma termSubst_cTV_LOR (w n : V) : termSubst ℒₒᵣ w (cTV n) = cTV n :=
  termSubst_eq_self_of_closed (cTV_semiterm 0 n)

lemma termSubst_cTV (w n : V) : termSubst LAct w (cTV n) = cTV n :=
  termSubst_eq_self_of_closed (cTV_semiterm_LAct 0 n)

lemma termBShift_cTV_LOR (n : V) : termBShift ℒₒᵣ (cTV n) = cTV n :=
  termBShift_eq_self_of_closed (cTV_semiterm 0 n)

lemma termBShift_cTV (n : V) : termBShift LAct (cTV n) = cTV n :=
  termBShift_eq_self_of_closed (cTV_semiterm_LAct 0 n)

/-! ### The standard chain numeral `cT` and the meta term `cTT` -/

/-- The chain numeral of a STANDARD `n`, as a code. -/
noncomputable def cT (n : ℕ) : V := cTV (n : V)

@[simp] lemma cT_zero : cT 0 = (𝟎 : V) := by simp [cT]
@[simp] lemma cT_succ (n : ℕ) : cT (n + 1) = (cT n : V) ^+ 𝟏 := by simp [cT]

lemma cT_semiterm (k : V) (n : ℕ) : IsSemiterm ℒₒᵣ k (cT n : V) := cTV_semiterm k _
lemma cT_semiterm_LAct (k : V) (n : ℕ) : IsSemiterm LAct k (cT n : V) := cTV_semiterm_LAct k _
lemma termLen_cT (n : ℕ) : termLen LAct (cT n : V) = 2 * (n : V) + 1 := termLen_cTV _
lemma termShift_cT (n : ℕ) : termShift LAct (cT n : V) = cT n := termShift_cTV _
lemma termSubst_cT (w : V) (n : ℕ) : termSubst LAct w (cT n : V) = cT n := termSubst_cTV w _
lemma fvOcc_cT (n : ℕ) : fvOcc LAct (cT n : V) = 0 := fvOcc_cTV _

/-- The meta chain term `0 + 1 + ⋯ + 1` (`n` ones) — what the DSL literal `0 + 1 + 1` is. -/
noncomputable def cTT : ℕ → ClosedSemiterm ℒₒᵣ 0
  | 0 => ‘0’
  | n + 1 => ‘!!(cTT n) + 1’

lemma cTT_zero : cTT 0 = ‘0’ := rfl
lemma cTT_succ (n : ℕ) : cTT (n + 1) = ‘!!(cTT n) + 1’ := rfl

/-- **The code equation**: the meta chain term's code is `cT n`, in every model. -/
theorem quote_cTT (n : ℕ) : (⌜cTT n⌝ : V) = cT n := by
  induction n with
  | zero => rw [cTT_zero, quote_closed_zero, cT_zero]
  | succ n ih =>
    rw [cTT_succ, show (‘!!(cTT n) + 1’ : ClosedSemiterm ℒₒᵣ 0) =
        ‘!!(cTT n) + !!(‘1’ : ClosedSemiterm ℒₒᵣ 0)’ from rfl,
      quote_closed_add, quote_closed_one, ih, cT_succ]

/-- The closed symbol rows of `Lib/Walk.lean` are the predicates at chain terms (`rfl`). -/
example : isRelConst_eqB = (↑LAct.isRel : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 0] := rfl
example : isRelConst_ltB = (↑LAct.isRel : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 1] := rfl
example : isFuncConst_zeroB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 0] := rfl
example : isFuncConst_oneB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 1] := rfl
example : isFuncConst_addB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 0] := rfl
example : isFuncConst_mulB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 2, cTT 1] := rfl
example : isFuncConst_cCB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 2] := rfl
example : isFuncConst_cDB = (↑LAct.isFunc : ArithmeticSemisentence 2) ⇜ ![cTT 0, cTT 3] := rfl

end cT

/-! ## 2. `bvOcc` — bound-variable occurrence counts — and the substitution occurrence bound -/

section bvOcc

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace BvOcc

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 1”
  fvar := .mkSigma “y x. y = 0”
  func := .mkSigma “y k f v v'. ∃ s, !listSumDef s v' ∧ y = s”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ _)        := 1
  fvar (_ _)        := 0
  func (_ _ _ _ v') := listSum v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end BvOcc

variable (L)

/-- Number of bound-variable occurrences (`qqBvar` nodes) in a term code. -/
noncomputable def bvOcc (t : V) : V := BvOcc.construction.result L ![] t

noncomputable def bvOccVec (k v : V) : V := BvOcc.construction.resultVec L ![] k v

noncomputable def bvOccGraph : 𝚺₁.Semisentence 2 := BvOcc.blueprint.result L

noncomputable def bvOccVecGraph : 𝚺₁.Semisentence 3 := BvOcc.blueprint.resultVec L

variable {L}

@[simp] lemma bvOcc_bvar (z : V) : bvOcc L ^#z = 1 := by simp [bvOcc, BvOcc.construction]

@[simp] lemma bvOcc_fvar (x : V) : bvOcc L ^&x = 0 := by simp [bvOcc, BvOcc.construction]

@[simp] lemma bvOcc_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    bvOcc L (^func k f v) = listSum (bvOccVec L k v) := by
  simp [bvOcc, BvOcc.construction, hkf, hv]; rfl

@[simp] lemma len_bvOccVec {k v : V} (hv : IsUTermVec L k v) :
    len (bvOccVec L k v) = k := BvOcc.construction.resultVec_lh L _ hv

@[simp] lemma nth_bvOccVec {k v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) :
    (bvOccVec L k v).[i] = bvOcc L v.[i] := BvOcc.construction.nth_resultVec L _ hv hi

@[simp] lemma bvOccVec_nil : bvOccVec L (0 : V) 0 = 0 := BvOcc.construction.resultVec_nil L _

lemma bvOccVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    bvOccVec L (k + 1) (t ∷ ts) = bvOcc L t ∷ bvOccVec L k ts :=
  BvOcc.construction.resultVec_cons L ![] hts ht

instance bvOcc.defined : 𝚺₁-Function₁ (bvOcc (V := V) L) via (bvOccGraph L) :=
  BvOcc.construction.result_defined

instance bvOcc.definable : 𝚺₁-Function₁ (bvOcc (V := V) L) := bvOcc.defined.to_definable

instance bvOcc.definable' : Γ-[k + 1]-Function₁ (bvOcc (V := V) L) :=
  bvOcc.definable.of_sigmaOne

instance bvOccVec.defined : 𝚺₁-Function₂ (bvOccVec (V := V) L) via (bvOccVecGraph L) :=
  BvOcc.construction.resultVec_defined

instance bvOccVec.definable : 𝚺₁-Function₂ (bvOccVec (V := V) L) :=
  bvOccVec.defined.to_definable

instance bvOccVec.definable' : Γ-[i + 1]-Function₂ (bvOccVec (V := V) L) :=
  bvOccVec.definable.of_sigmaOne

/-- Every bound-variable occurrence is a symbol: `bvOcc t ≤ termLen t`. -/
lemma bvOcc_le_termLen {t : V} (ht : IsUTerm L t) : bvOcc L t ≤ termLen L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [bvOcc_bvar, termLen_bvar]; exact le_add_self
  · intro x; rw [bvOcc_fvar, termLen_fvar]; exact zero_le
  · intro k f v hf hv ih
    rw [bvOcc_func hf hv, termLen_func hf hv]
    refine le_trans (listSum_le_of_nth (by rw [len_bvOccVec hv, len_termLenVec hv]) fun i hi ↦ ?_)
      le_self_add
    rw [len_bvOccVec hv] at hi
    rw [nth_bvOccVec hv hi, nth_termLenVec hv hi]
    exact ih i hi

/-- `termShift` preserves the number of bound-variable occurrences. -/
lemma bvOcc_termShift {t : V} (ht : IsUTerm L t) : bvOcc L (termShift L t) = bvOcc L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [termShift_bvar]
  · intro x; rw [termShift_fvar, bvOcc_fvar, bvOcc_fvar]
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
    rw [termShift_func hf hv, bvOcc_func hf hv', bvOcc_func hf hv]
    refine listSum_eq_of_nth (by rw [len_bvOccVec hv', len_bvOccVec hv]) fun i hi ↦ ?_
    rw [len_bvOccVec hv'] at hi
    rw [nth_bvOccVec hv' hi, nth_bvOccVec hv hi, nth_termShiftVec hv hi]
    exact ih i hi

/-- `termBShift` (bump every bound variable) preserves the number of FREE-variable occurrences. -/
lemma fvOcc_termBShift {t : V} (ht : IsUTerm L t) : fvOcc L (termBShift L t) = fvOcc L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [termBShift_bvar, fvOcc_bvar, fvOcc_bvar]
  · intro x; rw [termBShift_fvar]
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termBShiftVec L k v) := hv.termBShiftVec
    rw [termBShift_func hf hv, fvOcc_func hf hv', fvOcc_func hf hv]
    refine listSum_eq_of_nth (by rw [len_fvOccVec hv', len_fvOccVec hv]) fun i hi ↦ ?_
    rw [len_fvOccVec hv'] at hi
    rw [nth_fvOccVec hv' hi, nth_fvOccVec hv hi, nth_termBShiftVec hv hi]
    exact ih i hi

/-- Entry-wise `a.[i] ≤ b.[i] + c.[i]·M` gives `Σ a ≤ Σ b + (Σ c)·M`. -/
lemma listSum_le_add_mul {M : V} {a : V} :
    ∀ b c : V, len a = len b → len a = len c → (∀ i < len a, a.[i] ≤ b.[i] + c.[i] * M) →
      listSum a ≤ listSum b + listSum c * M := by
  induction a using adjoin_ISigma1.pi1_succ_induction with
  | hP => definability
  | nil =>
    intro b c hb hc _
    rcases nil_or_adjoin b with rfl | ⟨y, b', rfl⟩
    · rcases nil_or_adjoin c with rfl | ⟨z, c', rfl⟩
      · simp
      · simp at hc
    · simp at hb
  | adjoin x a ih =>
    intro b c hb hc h
    rcases nil_or_adjoin b with rfl | ⟨y, b', rfl⟩
    · simp at hb
    rcases nil_or_adjoin c with rfl | ⟨z, c', rfl⟩
    · simp at hc
    rw [len_adjoin, len_adjoin] at hb hc
    have hb' : len a = len b' := by simpa using hb
    have hc' : len a = len c' := by simpa using hc
    have h0 : x ≤ y + z * M := by simpa using h 0 (by simp)
    have hrest : ∀ i < len a, a.[i] ≤ b'.[i] + c'.[i] * M := fun i hi ↦ by
      simpa using h (i + 1) (by rw [len_adjoin]; simpa using hi)
    rw [listSum_adjoin, listSum_adjoin, listSum_adjoin]
    refine le_of_le_of_eq (add_le_add h0 (ih b' c' hb' hc' hrest)) ?_
    ring

/-- **The substitution occurrence bound for terms**: when every entry of `w` has at most `M`
free-variable occurrences, `termSubst w t` has at most `fvOcc t + bvOcc t · M` of them. -/
lemma fvOcc_termSubst_le {n m w M t : V} (ht : IsSemiterm L n t) (hw : IsSemitermVec L n m w)
    (hM : ∀ i < n, fvOcc L w.[i] ≤ M) :
    fvOcc L (termSubst L w t) ≤ fvOcc L t + bvOcc L t * M := by
  apply IsSemiterm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z hz
    rw [termSubst_bvar, fvOcc_bvar, bvOcc_bvar, zero_add, one_mul]
    exact hM z hz
  · intro x
    rw [termSubst_fvar, fvOcc_fvar, bvOcc_fvar, zero_mul, add_zero]
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [termSubst_func hf hv.isUTerm, fvOcc_func hf hv', fvOcc_func hf hv.isUTerm,
      bvOcc_func hf hv.isUTerm]
    refine listSum_le_add_mul _ _ (by rw [len_fvOccVec hv', len_fvOccVec hv.isUTerm])
      (by rw [len_fvOccVec hv', len_bvOccVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_fvOccVec hv'] at hi
    rw [nth_fvOccVec hv' hi, nth_fvOccVec hv.isUTerm hi, nth_bvOccVec hv.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi]
    exact ih i hi

/-- The entries of `qVec w` (`#0`, then `termBShift w.[i]`) inherit the occurrence bound. -/
lemma fvOcc_nth_qVec_le {n m w M : V} (hw : IsSemitermVec L n m w) (hM : ∀ i < n, fvOcc L w.[i] ≤ M) :
    ∀ i < n + 1, fvOcc L (qVec L w).[i] ≤ M := by
  intro i hi
  have hlen : len w = n := hw.lh
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · rw [qVec, nth_adjoin_zero, fvOcc_bvar]; exact zero_le
  · have hj : j < n := lt_of_add_lt_add_right hi
    rw [qVec, hlen, nth_adjoin_succ, nth_termBShiftVec hw.isUTerm hj, fvOcc_termBShift (hw.isUTerm.nth hj)]
    exact hM j hj

end bvOcc

/-! ### `bvOccF` — the formula count -/

section bvOccF

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace BvOccF

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(bvOccVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s”
  nrel := .mkSigma “y param k R v. ∃ M, !(bvOccVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂”
  all := .mkSigma “y param p₁ y₁. y = y₁”
  exs := .mkSigma “y param p₁ y₁. y = y₁”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listSum (bvOccVec L k v)
  nrel {_} := fun k _ v ↦ listSum (bvOccVec L k v)
  verum {_} := 0
  falsum {_} := 0
  and {_} := fun _ _ y₁ y₂ ↦ y₁ + y₂
  or {_} := fun _ _ y₁ y₂ ↦ y₁ + y₂
  all {_} := fun _ y₁ ↦ y₁
  exs {_} := fun _ y₁ ↦ y₁
  allChanges := fun _ ↦ 0
  exsChanges := fun _ ↦ 0
  rel_defined := .mk fun v ↦ by simp [blueprint]
  nrel_defined := .mk fun v ↦ by simp [blueprint]
  verum_defined := .mk fun v ↦ by simp [blueprint]
  falsum_defined := .mk fun v ↦ by simp [blueprint]
  and_defined := .mk fun v ↦ by simp [blueprint]
  or_defined := .mk fun v ↦ by simp [blueprint]
  all_defined := .mk fun v ↦ by simp [blueprint]
  exs_defined := .mk fun v ↦ by simp [blueprint]
  allChanges_defined := .mk fun v ↦ by simp [blueprint]
  exChanges_defined := .mk fun v ↦ by simp [blueprint]

end BvOccF

variable (L)

/-- Number of bound-variable occurrences in a formula code (ALL of them, whichever quantifier
binds them: atoms sum over the argument vector, connectives add, quantifiers pass through). -/
noncomputable def bvOccF (p : V) : V := (BvOccF.construction L).result L 0 p

noncomputable def bvOccFGraph : 𝚺₁.Semisentence 2 :=
  ((BvOccF.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

instance bvOccF.defined : 𝚺₁-Function₁ bvOccF (V := V) L via bvOccFGraph L := .mk fun v ↦ by
  simpa [bvOccFGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
    using! (BvOccF.construction L).result_defined.defined ![v 0, 0, v 1]

instance bvOccF.definable : 𝚺₁-Function₁ bvOccF (V := V) L := bvOccF.defined.to_definable

instance bvOccF.definable' : Γ-[m + 1]-Function₁ bvOccF (V := V) L :=
  bvOccF.definable.of_sigmaOne

@[simp] lemma bvOccF_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bvOccF L (^rel k R v) = listSum (bvOccVec L k v) := by
  simp [bvOccF, hR, hv, BvOccF.construction]

@[simp] lemma bvOccF_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    bvOccF L (^nrel k R v) = listSum (bvOccVec L k v) := by
  simp [bvOccF, hR, hv, BvOccF.construction]

@[simp] lemma bvOccF_verum : bvOccF L (^⊤ : V) = 0 := by
  simp [bvOccF, BvOccF.construction]

@[simp] lemma bvOccF_falsum : bvOccF L (^⊥ : V) = 0 := by
  simp [bvOccF, BvOccF.construction]

@[simp] lemma bvOccF_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bvOccF L (p ^⋏ q) = bvOccF L p + bvOccF L q := by
  simp [bvOccF, hp, hq, BvOccF.construction]

@[simp] lemma bvOccF_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    bvOccF L (p ^⋎ q) = bvOccF L p + bvOccF L q := by
  simp [bvOccF, hp, hq, BvOccF.construction]

@[simp] lemma bvOccF_all {p : V} (hp : IsUFormula L p) :
    bvOccF L (^∀ p) = bvOccF L p := by
  simp [bvOccF, hp, BvOccF.construction]

@[simp] lemma bvOccF_exs {p : V} (hp : IsUFormula L p) :
    bvOccF L (^∃ p) = bvOccF L p := by
  simp [bvOccF, hp, BvOccF.construction]

lemma listSum_bvOccVec_le {k v : V} (hv : IsUTermVec L k v) :
    listSum (bvOccVec L k v) ≤ listSum (termLenVec L k v) := by
  refine listSum_le_of_nth (by rw [len_bvOccVec hv, len_termLenVec hv]) fun i hi ↦ ?_
  rw [len_bvOccVec hv] at hi
  rw [nth_bvOccVec hv hi, nth_termLenVec hv hi]
  exact bvOcc_le_termLen (hv.nth hi)

lemma listSum_bvOccVec_termShiftVec {k v : V} (hv : IsUTermVec L k v) :
    listSum (bvOccVec L k (termShiftVec L k v)) = listSum (bvOccVec L k v) := by
  have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
  refine listSum_eq_of_nth (by rw [len_bvOccVec hv', len_bvOccVec hv]) fun i hi ↦ ?_
  rw [len_bvOccVec hv'] at hi
  rw [nth_bvOccVec hv' hi, nth_bvOccVec hv hi, nth_termShiftVec hv hi]
  exact bvOcc_termShift (hv.nth hi)

/-- `bvOccF p ≤ formulaLen p`. -/
lemma bvOccF_le_formulaLen {p : V} (hp : IsUFormula L p) : bvOccF L p ≤ formulaLen L p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [bvOccF_rel hR hv, formulaLen_rel hR hv]
    exact le_trans (listSum_bvOccVec_le hv) le_self_add
  · intro k R v hR hv
    rw [bvOccF_nrel hR hv, formulaLen_nrel hR hv]
    exact le_trans (listSum_bvOccVec_le hv) le_self_add
  · rw [bvOccF_verum]; exact zero_le
  · rw [bvOccF_falsum]; exact zero_le
  · intro p q hp hq ihp ihq
    rw [bvOccF_and hp hq, formulaLen_and hp hq]
    exact le_trans (add_le_add ihp ihq) le_self_add
  · intro p q hp hq ihp ihq
    rw [bvOccF_or hp hq, formulaLen_or hp hq]
    exact le_trans (add_le_add ihp ihq) le_self_add
  · intro p hp ih
    rw [bvOccF_all hp, formulaLen_all hp]
    exact le_trans ih le_self_add
  · intro p hp ih
    rw [bvOccF_exs hp, formulaLen_exs hp]
    exact le_trans ih le_self_add

/-- `shift` preserves the number of bound-variable occurrences. -/
lemma bvOccF_shift {p : V} (hp : IsUFormula L p) : bvOccF L (shift L p) = bvOccF L p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, bvOccF_rel hR hv.termShiftVec, bvOccF_rel hR hv,
      listSum_bvOccVec_termShiftVec hv]
  · intro k R v hR hv
    rw [shift_nrel hR hv, bvOccF_nrel hR hv.termShiftVec, bvOccF_nrel hR hv,
      listSum_bvOccVec_termShiftVec hv]
  · rw [shift_verum]
  · rw [shift_falsum]
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, bvOccF_and hp.shift hq.shift, bvOccF_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, bvOccF_or hp.shift hq.shift, bvOccF_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [shift_all hp, bvOccF_all hp.shift, bvOccF_all hp, ih]
  · intro p hp ih
    rw [shift_exs hp, bvOccF_exs hp.shift, bvOccF_exs hp, ih]

/-- The induction: every bound-variable occurrence of `p` — including those under inner
quantifiers, whose substitutes `#0`/`termBShift w.[i]` obey the same bound — is replaced by an
entry of `w`, free variables stay. -/
private lemma fvOccF_subst_le_aux {n p : V} (hp : IsSemiformula L n p) :
    ∀ m w M : V, IsSemitermVec L n m w → (∀ i < n, fvOcc L w.[i] ≤ M) →
      fvOccF L (subst L w p) ≤ fvOccF L p + bvOccF L p * M := by
  apply IsSemiformula.pi1_structural_induction
    (P := fun n p ↦ ∀ m w M : V, IsSemitermVec L n m w → (∀ i < n, fvOcc L w.[i] ≤ M) →
      fvOccF L (subst L w p) ≤ fvOccF L p + bvOccF L p * M) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k R v hR hv m w M hw hM
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [substs_rel hR hv.isUTerm, fvOccF_rel hR hv', fvOccF_rel hR hv.isUTerm, bvOccF_rel hR hv.isUTerm]
    refine listSum_le_add_mul _ _ (by rw [len_fvOccVec hv', len_fvOccVec hv.isUTerm])
      (by rw [len_fvOccVec hv', len_bvOccVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_fvOccVec hv'] at hi
    rw [nth_fvOccVec hv' hi, nth_fvOccVec hv.isUTerm hi, nth_bvOccVec hv.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi]
    exact fvOcc_termSubst_le (hv.nth hi) hw hM
  · intro n k R v hR hv m w M hw hM
    have hv' : IsUTermVec L k (termSubstVec L k w v) := (hw.termSubstVec hv).isUTerm
    rw [substs_nrel hR hv.isUTerm, fvOccF_nrel hR hv', fvOccF_nrel hR hv.isUTerm, bvOccF_nrel hR hv.isUTerm]
    refine listSum_le_add_mul _ _ (by rw [len_fvOccVec hv', len_fvOccVec hv.isUTerm])
      (by rw [len_fvOccVec hv', len_bvOccVec hv.isUTerm]) fun i hi ↦ ?_
    rw [len_fvOccVec hv'] at hi
    rw [nth_fvOccVec hv' hi, nth_fvOccVec hv.isUTerm hi, nth_bvOccVec hv.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi]
    exact fvOcc_termSubst_le (hv.nth hi) hw hM
  · intro n m w M _ _
    rw [substs_verum, fvOccF_verum, bvOccF_verum, zero_mul, add_zero]
  · intro n m w M _ _
    rw [substs_falsum, fvOccF_falsum, bvOccF_falsum, zero_mul, add_zero]
  · intro n p q hp hq ihp ihq m w M hw hM
    rw [substs_and hp.isUFormula hq.isUFormula,
      fvOccF_and (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvOccF_and hp.isUFormula hq.isUFormula, bvOccF_and hp.isUFormula hq.isUFormula]
    refine le_of_le_of_eq (add_le_add (ihp m w M hw hM) (ihq m w M hw hM)) ?_
    ring
  · intro n p q hp hq ihp ihq m w M hw hM
    rw [substs_or hp.isUFormula hq.isUFormula,
      fvOccF_or (hp.subst hw).isUFormula (hq.subst hw).isUFormula,
      fvOccF_or hp.isUFormula hq.isUFormula, bvOccF_or hp.isUFormula hq.isUFormula]
    refine le_of_le_of_eq (add_le_add (ihp m w M hw hM) (ihq m w M hw hM)) ?_
    ring
  · intro n p hp ih m w M hw hM
    rw [substs_all hp.isUFormula, fvOccF_all (hp.subst hw.qVec).isUFormula,
      fvOccF_all hp.isUFormula, bvOccF_all hp.isUFormula]
    exact ih _ _ _ hw.qVec (fvOcc_nth_qVec_le hw hM)
  · intro n p hp ih m w M hw hM
    rw [substs_ex hp.isUFormula, fvOccF_exs (hp.subst hw.qVec).isUFormula,
      fvOccF_exs hp.isUFormula, bvOccF_exs hp.isUFormula]
    exact ih _ _ _ hw.qVec (fvOcc_nth_qVec_le hw hM)

/-- **The substitution occurrence bound**: when every entry of `w` has at most `M` free-variable
occurrences, `subst w p` has at most `fvOccF p + bvOccF p · M` of them. -/
theorem fvOccF_subst_le {n p m w M : V} (hp : IsSemiformula L n p) (hw : IsSemitermVec L n m w)
    (hM : ∀ i < n, fvOcc L w.[i] ≤ M) :
    fvOccF L (subst L w p) ≤ fvOccF L p + bvOccF L p * M :=
  fvOccF_subst_le_aux hp m w M hw hM

/-- **The sharpened `free` bound**: `fvOccF (free p) ≤ fvOccF p + bvOccF p` (`ShiftLen.lean`'s
`fvOccF_free_le` charged `formulaLen p`) — `free p = (shift p)[#0 := &0]` with `?[&0]` a
vector whose single entry has ONE free-variable occurrence. -/
theorem fvOccF_free_le' {p : V} (hp : IsSemiformula L 1 p) :
    fvOccF L (free L p) ≤ fvOccF L p + bvOccF L p := by
  have hw : IsSemitermVec L 1 0 (^&0 ∷ (0 : V)) := by simp
  have hM : ∀ i < (1 : V), fvOcc L (^&0 ∷ (0 : V)).[i] ≤ 1 := fun i hi ↦ by
    rw [lt_one_iff_eq_zero] at hi
    subst hi
    rw [nth_adjoin_zero, fvOcc_fvar]
  have h := fvOccF_subst_le hp.shift hw hM
  rw [fvOccF_shift hp.isUFormula, bvOccF_shift hp.isUFormula, mul_one] at h
  unfold free substs1
  exact h

end bvOccF

/-! ## 3. Row instantiation at closed witnesses, any width -/

section instBv

/-- **The general reading**: `instOuterAt k es` on `subst ?[#i₁, …, #i_N] P` is
`subst ?[slot i₁, …, slot i_N] P` with `slot i = (bvarList k ++ es.reverse).getD i 0` — the
`k` innermost bound variables stay, the row's variables are read off `es` RIGHT-TO-LEFT. -/
theorem instOuterAt_subst_bvList (k : ℕ) {P : V} (is : List ℕ)
    (hP : IsSemiformula LAct ((is.length : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (his : ∀ i ∈ is, i < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec (is.map bv)) P) =
      subst LAct (listToVec (is.map fun i ↦ (bvarList k ++ es.reverse).getD i 0)) P := by
  have hW : IsSemitermVec LAct ((is.length : ℕ) : V) ((es.length + k : ℕ) : V) (listToVec (is.map bv)) := by
    have := isSemitermVec_listToVec (L := LAct) (n := ((es.length + k : ℕ) : V)) (is.map bv) (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact isSemiterm_bv (his i hi))
    rwa [List.length_map] at this
  rw [instOuterAt_subst k es hP hW hes]
  have h := termSubstVec_listToVec (L := LAct) (listToVec (bvarList k ++ es.reverse)) (is.map bv) (by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    simp)
  rw [List.length_map] at h
  rw [h, List.map_map]
  congr 2
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, bv]
  rw [termSubst_bvar, nth_listToVec]

theorem instOuter_subst_bvList {P : V} (is : List ℕ)
    (hP : IsSemiformula LAct ((is.length : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) (his : ∀ i ∈ is, i < es.length) :
    instOuter LAct es (subst LAct (listToVec (is.map bv)) P) =
      subst LAct (listToVec (is.map fun i ↦ es.reverse.getD i 0)) P := by
  rw [← instOuterAt_zero, instOuterAt_subst_bvList 0 is hP es hes (by simpa using his)]
  simp [bvarList]

/-- The literal-width readings (`Steps.lean` has `N = 2, 3`). -/
lemma instOuterAt_subst_bv1 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((1 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 : ℕ} (h1 : i1 < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i1]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i1 0]) P := by
  have := instOuterAt_subst_bvList k [i1] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i rfl; assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuter_subst_bv1 {P : V} (hP : IsSemiformula LAct ((1 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 : ℕ} (h1 : i1 < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i1]) P) =
      subst LAct (listToVec [es.reverse.getD i1 0]) P := by
  have := instOuter_subst_bvList [i1] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i rfl; assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuterAt_subst_bv4 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((4 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 : ℕ} (h1 : i1 < es.length + k) (h2 : i2 < es.length + k) (h3 : i3 < es.length + k) (h4 : i4 < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i1 0, (bvarList k ++ es.reverse).getD i2 0, (bvarList k ++ es.reverse).getD i3 0, (bvarList k ++ es.reverse).getD i4 0]) P := by
  have := instOuterAt_subst_bvList k [i1, i2, i3, i4] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuter_subst_bv4 {P : V} (hP : IsSemiformula LAct ((4 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 : ℕ} (h1 : i1 < es.length) (h2 : i2 < es.length) (h3 : i3 < es.length) (h4 : i4 < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4]) P) =
      subst LAct (listToVec [es.reverse.getD i1 0, es.reverse.getD i2 0, es.reverse.getD i3 0, es.reverse.getD i4 0]) P := by
  have := instOuter_subst_bvList [i1, i2, i3, i4] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuterAt_subst_bv5 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((5 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 : ℕ} (h1 : i1 < es.length + k) (h2 : i2 < es.length + k) (h3 : i3 < es.length + k) (h4 : i4 < es.length + k) (h5 : i5 < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i1 0, (bvarList k ++ es.reverse).getD i2 0, (bvarList k ++ es.reverse).getD i3 0, (bvarList k ++ es.reverse).getD i4 0, (bvarList k ++ es.reverse).getD i5 0]) P := by
  have := instOuterAt_subst_bvList k [i1, i2, i3, i4, i5] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuter_subst_bv5 {P : V} (hP : IsSemiformula LAct ((5 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 : ℕ} (h1 : i1 < es.length) (h2 : i2 < es.length) (h3 : i3 < es.length) (h4 : i4 < es.length) (h5 : i5 < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5]) P) =
      subst LAct (listToVec [es.reverse.getD i1 0, es.reverse.getD i2 0, es.reverse.getD i3 0, es.reverse.getD i4 0, es.reverse.getD i5 0]) P := by
  have := instOuter_subst_bvList [i1, i2, i3, i4, i5] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuterAt_subst_bv6 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((6 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 i6 : ℕ} (h1 : i1 < es.length + k) (h2 : i2 < es.length + k) (h3 : i3 < es.length + k) (h4 : i4 < es.length + k) (h5 : i5 < es.length + k) (h6 : i6 < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5, bv i6]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i1 0, (bvarList k ++ es.reverse).getD i2 0, (bvarList k ++ es.reverse).getD i3 0, (bvarList k ++ es.reverse).getD i4 0, (bvarList k ++ es.reverse).getD i5 0, (bvarList k ++ es.reverse).getD i6 0]) P := by
  have := instOuterAt_subst_bvList k [i1, i2, i3, i4, i5, i6] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuter_subst_bv6 {P : V} (hP : IsSemiformula LAct ((6 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 i6 : ℕ} (h1 : i1 < es.length) (h2 : i2 < es.length) (h3 : i3 < es.length) (h4 : i4 < es.length) (h5 : i5 < es.length) (h6 : i6 < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5, bv i6]) P) =
      subst LAct (listToVec [es.reverse.getD i1 0, es.reverse.getD i2 0, es.reverse.getD i3 0, es.reverse.getD i4 0, es.reverse.getD i5 0, es.reverse.getD i6 0]) P := by
  have := instOuter_subst_bvList [i1, i2, i3, i4, i5, i6] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuterAt_subst_bv7 (k : ℕ) {P : V} (hP : IsSemiformula LAct ((7 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 i6 i7 : ℕ} (h1 : i1 < es.length + k) (h2 : i2 < es.length + k) (h3 : i3 < es.length + k) (h4 : i4 < es.length + k) (h5 : i5 < es.length + k) (h6 : i6 < es.length + k) (h7 : i7 < es.length + k) :
    instOuterAt LAct k es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5, bv i6, bv i7]) P) =
      subst LAct (listToVec [(bvarList k ++ es.reverse).getD i1 0, (bvarList k ++ es.reverse).getD i2 0, (bvarList k ++ es.reverse).getD i3 0, (bvarList k ++ es.reverse).getD i4 0, (bvarList k ++ es.reverse).getD i5 0, (bvarList k ++ es.reverse).getD i6 0, (bvarList k ++ es.reverse).getD i7 0]) P := by
  have := instOuterAt_subst_bvList k [i1, i2, i3, i4, i5, i6, i7] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

lemma instOuter_subst_bv7 {P : V} (hP : IsSemiformula LAct ((7 : ℕ) : V) P) (es : List V)
    (hes : ∀ e ∈ es, IsSemiterm LAct 0 e) {i1 i2 i3 i4 i5 i6 i7 : ℕ} (h1 : i1 < es.length) (h2 : i2 < es.length) (h3 : i3 < es.length) (h4 : i4 < es.length) (h5 : i5 < es.length) (h6 : i6 < es.length) (h7 : i7 < es.length) :
    instOuter LAct es (subst LAct (listToVec [bv i1, bv i2, bv i3, bv i4, bv i5, bv i6, bv i7]) P) =
      subst LAct (listToVec [es.reverse.getD i1 0, es.reverse.getD i2 0, es.reverse.getD i3 0, es.reverse.getD i4 0, es.reverse.getD i5 0, es.reverse.getD i6 0, es.reverse.getD i7 0]) P := by
  have := instOuter_subst_bvList [i1, i2, i3, i4, i5, i6, i7] hP es hes (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro i (rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> assumption)
  simpa only [List.map_cons, List.map_nil] using this

end instBv

/-! ## 4. Iterated `free` — the existentials of a row conclusion, innermost last -/

section freeIter

variable {L : Language} [L.Encodable] [L.LORDefinable]

variable (L) in
/-- `freeIter k q`: `k` eigenvariable introductions on a `k`-semiformula `q`, from the OUTERMOST
quantifier inwards — each step frees the current outermost bound variable `#j` under the `j`
remaining ones (`subOuter j (&0) ∘ shift`, which is what `free` does to the body of `∃^j`,
`free_exsIter`). -/
noncomputable def freeIter : ℕ → V → V
  | 0, q => q
  | j + 1, q => freeIter j (subOuter L j (^&0) (shift L q))

@[simp] lemma freeIter_zero (q : V) : freeIter L 0 q = q := rfl
@[simp] lemma freeIter_succ (j : ℕ) (q : V) :
    freeIter L (j + 1) q = freeIter L j (subOuter L j (^&0) (shift L q)) := rfl

/-- One step is `free`. -/
lemma freeIter_one (q : V) : freeIter L 1 q = free L q := rfl

lemma subOuter_exsIter {n : ℕ} {e q : V} (hq : IsUFormula L q) : ∀ j : ℕ,
    subOuter L n e (exsIter j q) = exsIter j (subOuter L (n + j) e q)
  | 0 => rfl
  | j + 1 => by
    rw [exsIter_succ, subOuter_exs (isUFormula_exsIter.mpr hq), subOuter_exsIter hq j, exsIter_succ,
      show n + 1 + j = n + (j + 1) by omega]

lemma shift_exsIter {q : V} (hq : IsUFormula L q) : ∀ j : ℕ,
    shift L (exsIter j q) = exsIter j (shift L q)
  | 0 => rfl
  | j + 1 => by rw [exsIter_succ, shift_exs (isUFormula_exsIter.mpr hq), shift_exsIter hq j, exsIter_succ]

/-- **`free` under `j` existentials** is the `freeIter` step at depth `j`: `free (∃^j q) =
∃^j (subOuter j (&0) (shift q))`. -/
theorem free_exsIter {q : V} (hq : IsUFormula L q) : ∀ j : ℕ,
    free L (exsIter j q) = exsIter j (subOuter L j (^&0) (shift L q))
  | 0 => rfl
  | j + 1 => by
    rw [exsIter_succ, free_exs (isUFormula_exsIter.mpr hq), shift_exsIter hq j,
      show subst L (qVec L ?[^&0]) (exsIter j (shift L q)) =
        subOuter L 1 (^&0) (exsIter j (shift L q)) from rfl,
      subOuter_exsIter hq.shift j, exsIter_succ, Nat.add_comm]

/-- `[&0, …, &(k-1)]`. -/
noncomputable def fvarList (k : ℕ) : List V := (List.range k).map fun i ↦ ^&((i : ℕ) : V)

@[simp] lemma fvarList_zero : fvarList (V := V) 0 = [] := rfl
@[simp] lemma length_fvarList (k : ℕ) : (fvarList (V := V) k).length = k := by simp [fvarList]

lemma fvarList_succ (k : ℕ) : fvarList (V := V) (k + 1) = fvarList k ++ [^&((k : ℕ) : V)] := by
  simp [fvarList, List.range_succ]

lemma bvarList_succ (k : ℕ) : bvarList (V := V) (k + 1) = bvarList k ++ [^#((k : ℕ) : V)] := by
  simp [bvarList, List.range_succ]

lemma mem_bvarList {x : V} {k : ℕ} (hx : x ∈ bvarList (V := V) k) : ∃ i : ℕ, i < k ∧ x = ^#((i : ℕ) : V) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact ⟨i, List.mem_range.mp hi, rfl⟩

lemma map_termShift_bvarList (k : ℕ) : (bvarList (V := V) k).map (termShift L) = bvarList k := by
  simp [bvarList, List.map_map, Function.comp_def]

/-- `subOuter k (&0)` sends `#i ↦ #i` (`i < k`) and `#k ↦ &0`. -/
lemma map_termSubst_qVecIter_bvarList (k : ℕ) :
    (bvarList (V := V) (k + 1)).map (termSubst L (qVecIter L k (^&0 ∷ (0 : V)))) = bvarList k ++ [^&0] := by
  rw [bvarList_succ, List.map_append, List.map_singleton, termSubst_qVecIter_bvar_eq (by simp)]
  congr 1
  refine Eq.trans (List.map_congr_left (g := id) ?_) (List.map_id _)
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_bvarList hx
  exact termSubst_qVecIter_bvar_lt (by simp) hi

lemma termShift_iterate_fvar (x : V) : ∀ j : ℕ, (termShift L)^[j] (^&x) = ^&(x + (j : V))
  | 0 => by simp
  | j + 1 => by
    rw [Function.iterate_succ_apply, termShift_fvar, termShift_iterate_fvar (x + 1) j, Nat.cast_succ]
    ring_nf

/-- **Iterated `free` on a substituted closed code**: `freeIter k (subst ?[#0, …, #(k-1), l] P) =
subst ?[&0, …, &(k-1), termShift^k l] P` for closed `l` and `shift P = P` (a quoted sentence
code): the LAST-listed existential (`#0`, the innermost) becomes `&0`, the outermost `&(k-1)`,
and every closed witness is shifted once per introduction. -/
theorem freeIter_subst_listToVec {P : V} (hP0 : shift L P = P) : ∀ (k : ℕ) (l : List V),
    IsSemiformula L ((k + l.length : ℕ) : V) P → (∀ x ∈ l, IsSemiterm L 0 x) →
    freeIter L k (subst L (listToVec (bvarList k ++ l)) P) =
      subst L (listToVec (fvarList k ++ l.map (termShift L)^[k])) P
  | 0, l, _, _ => by simp [bvarList]
  | j + 1, l, hP, hl => by
    -- the current vector `[#0, …, #j] ++ l`, at level `j + 1`
    have hl1 : ∀ x ∈ bvarList (V := V) (j + 1) ++ l, IsSemiterm L ((j + 1 : ℕ) : V) x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := mem_bvarList hx
        exact IsSemiterm.bvar.mpr (Nat.cast_lt.mpr hi)
      · exact isSemiterm_of_le (hl x hx) zero_le
    have hlen1 : ((bvarList (V := V) (j + 1) ++ l).length : ℕ) = j + 1 + l.length := by simp
    have hP1 : IsSemiformula L (((bvarList (V := V) (j + 1) ++ l).length : ℕ) : V) P := by
      rw [hlen1]; exact hP
    rw [freeIter_succ, shift_subst_listToVec _ hP1 hP0 hl1, List.map_append, map_termShift_bvarList]
    -- the shifted vector `[#0, …, #j] ++ shift l`, still at level `j + 1`
    set l' := l.map (termShift L) with hl'
    have hl'c : ∀ x ∈ l', IsSemiterm L 0 x := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact (hl y hy).termShift
    have hl1' : ∀ x ∈ bvarList (V := V) (j + 1) ++ l', IsSemiterm L ((j : V) + 1) x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi, rfl⟩ := mem_bvarList hx
        exact IsSemiterm.bvar.mpr (by exact_mod_cast hi)
      · exact isSemiterm_of_le (hl'c x hx) zero_le
    have hlen' : ((bvarList (V := V) (j + 1) ++ l').length : ℕ) = j + 1 + l.length := by simp [hl']
    have hP' : IsSemiformula L (((bvarList (V := V) (j + 1) ++ l').length : ℕ) : V) P := by
      rw [hlen']; exact hP
    have hW : IsSemitermVec L (((bvarList (V := V) (j + 1) ++ l').length : ℕ) : V) ((j : V) + 1)
        (listToVec (bvarList (j + 1) ++ l')) := isSemitermVec_listToVec _ hl1'
    rw [subOuter_subst hP' hW (by simp), termSubstVec_listToVec _ _ (fun x hx ↦ (hl1' x hx).isUTerm),
      List.map_append, map_termSubst_qVecIter_bvarList,
      List.map_congr_left (fun x hx ↦ termSubst_eq_self_of_closed (hl'c x hx)), List.map_id',
      List.append_assoc, List.singleton_append]
    -- the induction hypothesis at `l := &0 :: shift l`
    have hP'' : IsSemiformula L ((j + (^&0 :: l').length : ℕ) : V) P := by
      rw [show j + (^&0 :: l').length = j + 1 + l.length by
        rw [List.length_cons, hl', List.length_map]; omega]
      exact hP
    have hl'' : ∀ x ∈ (^&0 :: l'), IsSemiterm L 0 x := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · exact hl'c x hx
    rw [freeIter_subst_listToVec hP0 j (^&0 :: l') hP'' hl'', List.map_cons, termShift_iterate_fvar,
      zero_add, hl', List.map_map, ← Function.iterate_succ, fvarList_succ, List.append_assoc,
      List.singleton_append]

end freeIter

end ArithS

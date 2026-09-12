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

end ArithS

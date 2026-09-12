import ArithS.Necessitation.Primitives

/-!
# ArithS.Necessitation.ShiftLen — free-variable occurrence counts and the ADDITIVE length
bound for `shift` / `setShift`

`Necessitation/Primitives.lean` bounds the symbol count of a shifted code by DOUBLING:
`termLen (termShift t) ≤ 2·termLen t`, `formulaLen (shift p) ≤ 2·formulaLen p`,
`setLen (setShift s) ≤ 2·setLen s`. Chained through `n` eigenvariable eliminations
(`elimExistsCode`, `introFactCode`) that composes to `2ⁿ` — the cost-accounting risk of
`M4_BOUNDED_HBL/BRIEF.md` §9 and `DESIGN_inner_necessitation.md` §3.7.

The doubling is an artefact of the bound, not of the shift: `shift` renames every free
variable `&x` to `&(x + 1)`, and free-variable indices are charged UNARY (`termLen_fvar :
termLen (^&x) = x + 1`, `Length.lean`), so ONE shift adds exactly ONE symbol per free-variable
OCCURRENCE and nothing else. This module makes that exact:

* `fvOcc L t` / `fvOccVec L k v` / `fvOccF L p` / `fvOccS L s` — the number of free-variable
  occurrences (`qqFvar` nodes) in a term / term vector / formula / formula-set code, Σ₁
  functions by the same recursion schemes as `termLen` / `formulaLen` / `setLen`
  (`TermRec`, `UformulaRec1`, primitive recursion over the bit-set), with `defined` /
  `definable` instances and one equation per constructor;
* the EXACT laws `termLen_termShift_eq : termLen (termShift t) = termLen t + fvOcc t`,
  `formulaLen_shift_eq : formulaLen (shift p) = formulaLen p + fvOccF p`, the set bound
  `setLen_setShift_le_occ : setLen (setShift s) ≤ setLen s + fvOccS s` (`≤` only because
  Foundation has no injectivity lemma for `shift` on codes; `setShift` might identify two
  members), and the invariances `fvOcc_termShift`, `fvOccF_shift`, `fvOccS_setShift_le`
  (again `≤`, for the same reason) — hence `n` shifts cost `n · fvOccS s`, LINEAR:
  `setLen_setShiftIter_le : setLen (setShiftIter n s) ≤ setLen s + n · fvOccS s`;
* the sanity bounds `fvOcc_le_termLen`, `fvOccF_le_formulaLen`, `fvOccS_le_setLen`, which
  recover the doubling bounds of `Primitives`, and `fvOccF_free_le : fvOccF (free p) ≤
  fvOccF p + formulaLen p` (`free` also instantiates `#0` by `&0`, once per `#0`-occurrence —
  a bound in terms of a bound-variable occurrence count is NOT delivered here, see the
  remark at the lemma);
* the restated primitive bound `dlen_elimExistsCode_le_occ`: `dlen (elimExistsCode Γ P D d) ≤
  dlen D + dlen d + 4·setLen Γ + fvOccS Γ + 6·formulaLen P + 8` — the `5·setLen Γ` of
  `dlen_elimExistsCode_le'` with the doubled context replaced by the additive term.

Everything is V-generic (any model of `IΣ₁`) and `L`-generic, three standard axioms.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open Classical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### `listSum` under entry-wise addition and entry-wise `≤` -/

/-- Entry-wise `a.[i] = b.[i] + c.[i]` gives `Σ a = Σ b + Σ c`. -/
lemma listSum_add_of_nth {a : V} :
    ∀ b c : V, len a = len b → len a = len c → (∀ i < len a, a.[i] = b.[i] + c.[i]) →
      listSum a = listSum b + listSum c := by
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
    have h0 : x = y + z := by simpa using h 0 (by simp)
    have hrest : ∀ i < len a, a.[i] = b'.[i] + c'.[i] := fun i hi ↦ by
      simpa using h (i + 1) (by rw [len_adjoin]; simpa using hi)
    rw [listSum_adjoin, listSum_adjoin, listSum_adjoin, h0, ih b' c' hb' hc' hrest]
    ring

/-- Entry-wise `a.[i] ≤ b.[i]` gives `Σ a ≤ Σ b`. -/
lemma listSum_le_of_nth {a b : V} (hl : len a = len b) (h : ∀ i < len a, a.[i] ≤ b.[i]) :
    listSum a ≤ listSum b := by
  have := listSum_le_mul (B := 1) (a := a) b hl (fun i hi ↦ by rw [mul_one]; exact h i hi)
  rwa [mul_one] at this

/-- Entry-wise equal vectors have equal sums. -/
lemma listSum_eq_of_nth {a b : V} (hl : len a = len b) (h : ∀ i < len a, a.[i] = b.[i]) :
    listSum a = listSum b :=
  le_antisymm (listSum_le_of_nth hl fun i hi ↦ le_of_eq (h i hi))
    (listSum_le_of_nth hl.symm fun i hi ↦ le_of_eq (h i (hl ▸ hi)).symm)

/-! ### Terms — `fvOcc` -/

section term

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FvOcc

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 0”
  fvar := .mkSigma “y x. y = 1”
  func := .mkSigma “y k f v v'. ∃ s, !listSumDef s v' ∧ y = s”

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ _)        := 0
  fvar (_ _)        := 1
  func (_ _ _ _ v') := listSum v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end FvOcc

open FvOcc

variable (L)

/-- Number of free-variable occurrences (`qqFvar` nodes) in a term code. -/
noncomputable def fvOcc (t : V) : V := construction.result L ![] t

noncomputable def fvOccVec (k v : V) : V := construction.resultVec L ![] k v

noncomputable def fvOccGraph : 𝚺₁.Semisentence 2 := blueprint.result L

noncomputable def fvOccVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp] lemma fvOcc_bvar (z : V) : fvOcc L ^#z = 0 := by simp [fvOcc, construction]

@[simp] lemma fvOcc_fvar (x : V) : fvOcc L ^&x = 1 := by simp [fvOcc, construction]

@[simp] lemma fvOcc_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    fvOcc L (^func k f v) = listSum (fvOccVec L k v) := by
  simp [fvOcc, construction, hkf, hv]; rfl

@[simp] lemma len_fvOccVec {k v : V} (hv : IsUTermVec L k v) :
    len (fvOccVec L k v) = k := construction.resultVec_lh L _ hv

@[simp] lemma nth_fvOccVec {k v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) :
    (fvOccVec L k v).[i] = fvOcc L v.[i] := construction.nth_resultVec L _ hv hi

@[simp] lemma fvOccVec_nil : fvOccVec L (0 : V) 0 = 0 := construction.resultVec_nil L _

lemma fvOccVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    fvOccVec L (k + 1) (t ∷ ts) = fvOcc L t ∷ fvOccVec L k ts :=
  construction.resultVec_cons L ![] hts ht

instance fvOcc.defined : 𝚺₁-Function₁ (fvOcc (V := V) L) via (fvOccGraph L) :=
  construction.result_defined

instance fvOcc.definable : 𝚺₁-Function₁ (fvOcc (V := V) L) := fvOcc.defined.to_definable

instance fvOcc.definable' : Γ-[k + 1]-Function₁ (fvOcc (V := V) L) :=
  fvOcc.definable.of_sigmaOne

instance fvOccVec.defined : 𝚺₁-Function₂ (fvOccVec (V := V) L) via (fvOccVecGraph L) :=
  construction.resultVec_defined

instance fvOccVec.definable : 𝚺₁-Function₂ (fvOccVec (V := V) L) :=
  fvOccVec.defined.to_definable

instance fvOccVec.definable' : Γ-[i + 1]-Function₂ (fvOccVec (V := V) L) :=
  fvOccVec.definable.of_sigmaOne

/-- Every free-variable occurrence is a symbol: `fvOcc t ≤ termLen t`. -/
lemma fvOcc_le_termLen {t : V} (ht : IsUTerm L t) : fvOcc L t ≤ termLen L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [fvOcc_bvar, termLen_bvar]; exact zero_le
  · intro x; rw [fvOcc_fvar, termLen_fvar]; exact le_add_self
  · intro k f v hf hv ih
    rw [fvOcc_func hf hv, termLen_func hf hv]
    refine le_trans (listSum_le_of_nth (by rw [len_fvOccVec hv, len_termLenVec hv]) fun i hi ↦ ?_)
      le_self_add
    rw [len_fvOccVec hv] at hi
    rw [nth_fvOccVec hv hi, nth_termLenVec hv hi]
    exact ih i hi

/-- **The exact law for terms**: `termShift` adds one symbol per free-variable occurrence. -/
lemma termLen_termShift_eq {t : V} (ht : IsUTerm L t) :
    termLen L (termShift L t) = termLen L t + fvOcc L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [termShift_bvar, fvOcc_bvar, add_zero]
  · intro x; rw [termShift_fvar, termLen_fvar, termLen_fvar, fvOcc_fvar]
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
    rw [termShift_func hf hv, termLen_func hf hv', termLen_func hf hv, fvOcc_func hf hv]
    have : listSum (termLenVec L k (termShiftVec L k v)) =
        listSum (termLenVec L k v) + listSum (fvOccVec L k v) := by
      refine listSum_add_of_nth _ _ (by rw [len_termLenVec hv', len_termLenVec hv])
        (by rw [len_termLenVec hv', len_fvOccVec hv]) fun i hi ↦ ?_
      rw [len_termLenVec hv'] at hi
      rw [nth_termLenVec hv' hi, nth_termLenVec hv hi, nth_fvOccVec hv hi, nth_termShiftVec hv hi]
      exact ih i hi
    rw [this]; ring

/-- `termShift` preserves the number of free-variable occurrences. -/
lemma fvOcc_termShift {t : V} (ht : IsUTerm L t) : fvOcc L (termShift L t) = fvOcc L t := by
  apply IsUTerm.induction 𝚷 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; rw [termShift_bvar]
  · intro x; rw [termShift_fvar, fvOcc_fvar, fvOcc_fvar]
  · intro k f v hf hv ih
    have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
    rw [termShift_func hf hv, fvOcc_func hf hv', fvOcc_func hf hv]
    refine listSum_eq_of_nth (by rw [len_fvOccVec hv', len_fvOccVec hv]) fun i hi ↦ ?_
    rw [len_fvOccVec hv'] at hi
    rw [nth_fvOccVec hv' hi, nth_fvOccVec hv hi, nth_termShiftVec hv hi]
    exact ih i hi

/-- The vector forms of the three term laws, as sums. -/
lemma listSum_fvOccVec_le {k v : V} (hv : IsUTermVec L k v) :
    listSum (fvOccVec L k v) ≤ listSum (termLenVec L k v) := by
  refine listSum_le_of_nth (by rw [len_fvOccVec hv, len_termLenVec hv]) fun i hi ↦ ?_
  rw [len_fvOccVec hv] at hi
  rw [nth_fvOccVec hv hi, nth_termLenVec hv hi]
  exact fvOcc_le_termLen (hv.nth hi)

lemma listSum_termLenVec_termShiftVec_eq {k v : V} (hv : IsUTermVec L k v) :
    listSum (termLenVec L k (termShiftVec L k v)) =
      listSum (termLenVec L k v) + listSum (fvOccVec L k v) := by
  have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
  refine listSum_add_of_nth _ _ (by rw [len_termLenVec hv', len_termLenVec hv])
    (by rw [len_termLenVec hv', len_fvOccVec hv]) fun i hi ↦ ?_
  rw [len_termLenVec hv'] at hi
  rw [nth_termLenVec hv' hi, nth_termLenVec hv hi, nth_fvOccVec hv hi, nth_termShiftVec hv hi]
  exact termLen_termShift_eq (hv.nth hi)

lemma listSum_fvOccVec_termShiftVec {k v : V} (hv : IsUTermVec L k v) :
    listSum (fvOccVec L k (termShiftVec L k v)) = listSum (fvOccVec L k v) := by
  have hv' : IsUTermVec L k (termShiftVec L k v) := hv.termShiftVec
  refine listSum_eq_of_nth (by rw [len_fvOccVec hv', len_fvOccVec hv]) fun i hi ↦ ?_
  rw [len_fvOccVec hv'] at hi
  rw [nth_fvOccVec hv' hi, nth_fvOccVec hv hi, nth_termShiftVec hv hi]
  exact fvOcc_termShift (hv.nth hi)

end term

/-! ### Formulas — `fvOccF` -/

section formula

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FvOccF

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(fvOccVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s”
  nrel := .mkSigma “y param k R v. ∃ M, !(fvOccVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s”
  verum := .mkSigma “y param. y = 0”
  falsum := .mkSigma “y param. y = 0”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂”
  all := .mkSigma “y param p₁ y₁. y = y₁”
  exs := .mkSigma “y param p₁ y₁. y = y₁”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listSum (fvOccVec L k v)
  nrel {_} := fun k _ v ↦ listSum (fvOccVec L k v)
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

end FvOccF

variable (L)

/-- Number of free-variable occurrences in a formula code (atoms: the sum over the argument
vector; connectives add; quantifiers pass through). -/
noncomputable def fvOccF (p : V) : V := (FvOccF.construction L).result L 0 p

noncomputable def fvOccFGraph : 𝚺₁.Semisentence 2 :=
  ((FvOccF.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

instance fvOccF.defined : 𝚺₁-Function₁ fvOccF (V := V) L via fvOccFGraph L := .mk fun v ↦ by
  simpa [fvOccFGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
    using! (FvOccF.construction L).result_defined.defined ![v 0, 0, v 1]

instance fvOccF.definable : 𝚺₁-Function₁ fvOccF (V := V) L := fvOccF.defined.to_definable

instance fvOccF.definable' : Γ-[m + 1]-Function₁ fvOccF (V := V) L :=
  fvOccF.definable.of_sigmaOne

@[simp] lemma fvOccF_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvOccF L (^rel k R v) = listSum (fvOccVec L k v) := by
  simp [fvOccF, hR, hv, FvOccF.construction]

@[simp] lemma fvOccF_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    fvOccF L (^nrel k R v) = listSum (fvOccVec L k v) := by
  simp [fvOccF, hR, hv, FvOccF.construction]

@[simp] lemma fvOccF_verum : fvOccF L (^⊤ : V) = 0 := by
  simp [fvOccF, FvOccF.construction]

@[simp] lemma fvOccF_falsum : fvOccF L (^⊥ : V) = 0 := by
  simp [fvOccF, FvOccF.construction]

@[simp] lemma fvOccF_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvOccF L (p ^⋏ q) = fvOccF L p + fvOccF L q := by
  simp [fvOccF, hp, hq, FvOccF.construction]

@[simp] lemma fvOccF_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    fvOccF L (p ^⋎ q) = fvOccF L p + fvOccF L q := by
  simp [fvOccF, hp, hq, FvOccF.construction]

@[simp] lemma fvOccF_all {p : V} (hp : IsUFormula L p) :
    fvOccF L (^∀ p) = fvOccF L p := by
  simp [fvOccF, hp, FvOccF.construction]

@[simp] lemma fvOccF_exs {p : V} (hp : IsUFormula L p) :
    fvOccF L (^∃ p) = fvOccF L p := by
  simp [fvOccF, hp, FvOccF.construction]

/-- `fvOccF p ≤ formulaLen p`. -/
lemma fvOccF_le_formulaLen {p : V} (hp : IsUFormula L p) : fvOccF L p ≤ formulaLen L p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [fvOccF_rel hR hv, formulaLen_rel hR hv]
    exact le_trans (listSum_fvOccVec_le hv) le_self_add
  · intro k R v hR hv
    rw [fvOccF_nrel hR hv, formulaLen_nrel hR hv]
    exact le_trans (listSum_fvOccVec_le hv) le_self_add
  · rw [fvOccF_verum]; exact zero_le
  · rw [fvOccF_falsum]; exact zero_le
  · intro p q hp hq ihp ihq
    rw [fvOccF_and hp hq, formulaLen_and hp hq]
    exact le_trans (add_le_add ihp ihq) le_self_add
  · intro p q hp hq ihp ihq
    rw [fvOccF_or hp hq, formulaLen_or hp hq]
    exact le_trans (add_le_add ihp ihq) le_self_add
  · intro p hp ih
    rw [fvOccF_all hp, formulaLen_all hp]
    exact le_trans ih le_self_add
  · intro p hp ih
    rw [fvOccF_exs hp, formulaLen_exs hp]
    exact le_trans ih le_self_add

/-- **The exact law for formulas**: `shift` adds one symbol per free-variable occurrence. -/
lemma formulaLen_shift_eq {p : V} (hp : IsUFormula L p) :
    formulaLen L (shift L p) = formulaLen L p + fvOccF L p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, formulaLen_rel hR hv.termShiftVec, formulaLen_rel hR hv, fvOccF_rel hR hv,
      listSum_termLenVec_termShiftVec_eq hv]
    ring
  · intro k R v hR hv
    rw [shift_nrel hR hv, formulaLen_nrel hR hv.termShiftVec, formulaLen_nrel hR hv, fvOccF_nrel hR hv,
      listSum_termLenVec_termShiftVec_eq hv]
    ring
  · rw [shift_verum, fvOccF_verum, add_zero]
  · rw [shift_falsum, fvOccF_falsum, add_zero]
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, formulaLen_and hp.shift hq.shift, formulaLen_and hp hq, fvOccF_and hp hq,
      ihp, ihq]
    ring
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, formulaLen_or hp.shift hq.shift, formulaLen_or hp hq, fvOccF_or hp hq,
      ihp, ihq]
    ring
  · intro p hp ih
    rw [shift_all hp, formulaLen_all hp.shift, formulaLen_all hp, fvOccF_all hp, ih]
    ring
  · intro p hp ih
    rw [shift_exs hp, formulaLen_exs hp.shift, formulaLen_exs hp, fvOccF_exs hp, ih]
    ring

/-- `shift` preserves the number of free-variable occurrences. -/
lemma fvOccF_shift {p : V} (hp : IsUFormula L p) : fvOccF L (shift L p) = fvOccF L p := by
  apply IsUFormula.ISigma1.pi1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv
    rw [shift_rel hR hv, fvOccF_rel hR hv.termShiftVec, fvOccF_rel hR hv,
      listSum_fvOccVec_termShiftVec hv]
  · intro k R v hR hv
    rw [shift_nrel hR hv, fvOccF_nrel hR hv.termShiftVec, fvOccF_nrel hR hv,
      listSum_fvOccVec_termShiftVec hv]
  · rw [shift_verum]
  · rw [shift_falsum]
  · intro p q hp hq ihp ihq
    rw [shift_and hp hq, fvOccF_and hp.shift hq.shift, fvOccF_and hp hq, ihp, ihq]
  · intro p q hp hq ihp ihq
    rw [shift_or hp hq, fvOccF_or hp.shift hq.shift, fvOccF_or hp hq, ihp, ihq]
  · intro p hp ih
    rw [shift_all hp, fvOccF_all hp.shift, fvOccF_all hp, ih]
  · intro p hp ih
    rw [shift_exs hp, fvOccF_exs hp.shift, fvOccF_exs hp, ih]

/-- The de Morgan dual has the same free-variable occurrences (`neg` swaps `rel/nrel`,
`⋏/⋎`, `∀/∃`). -/
lemma fvOccF_neg {p : V} (hp : IsUFormula L p) : fvOccF L (neg L p) = fvOccF L p := by
  apply IsUFormula.ISigma1.sigma1_succ_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k R v hR hv; simp [hR, hv]
  · intro k R v hR hv; simp [hR, hv]
  · simp
  · simp
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p q hp hq ihp ihq; simp [hp, hq, hp.neg, hq.neg, ihp, ihq]
  · intro p hp ihp; simp [hp, hp.neg, ihp]
  · intro p hp ihp; simp [hp, hp.neg, ihp]

/-- `fvOccF (free p) ≤ fvOccF p + formulaLen p`. `free p = (shift p)[#0 := &0]` adds one
free-variable occurrence per occurrence of `#0` in `p`; the count of THOSE is not a function
defined here, so the bound charges every symbol of `p` instead (`fvOccF ≤ formulaLen` on
`free p`, whose length is that of `shift p` — one-symbol term for one-symbol variable). -/
lemma fvOccF_free_le {p : V} (hp : IsSemiformula L 1 p) :
    fvOccF L (free L p) ≤ fvOccF L p + formulaLen L p := by
  have h1 : formulaLen L (subst L (^&0 ∷ (0 : V)) (shift L p)) ≤ formulaLen L (shift L p) * 1 :=
    formulaLen_subst_le (le_refl 1) hp.shift 0 (^&0 ∷ (0 : V)) (by simp)
      (substInv_single (by simp) (by simp))
  rw [mul_one, formulaLen_shift_eq hp.isUFormula] at h1
  refine le_trans (fvOccF_le_formulaLen hp.free.isUFormula) ?_
  unfold free substs1
  rw [add_comm]
  exact h1

end formula

/-! ### Formula sets — `fvOccS` (primitive recursion over the bit-set, like `setLen`) -/

section set

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FvOccS

variable (L)

/-- `zero s = 0`; `succ s i ih = ih + fvOccF i` if `i ∈ s`, else `ih`. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = 0”
  succ := .mkSigma “y ih i s. (i ∈ s → ∃ l, !(fvOccFGraph L) l i ∧ y = ih + l) ∧ (¬i ∈ s → y = ih)”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun _ ↦ 0
  succ := fun v i ih ↦ if i ∈ v 0 then ih + fvOccF L i else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    suffices
      (v 2 ∈ v 3 → v 0 = v 1 + fvOccF L (v 2)) ∧ (v 2 ∉ v 3 → v 0 = v 1) ↔
      (v 0 = if v 2 ∈ v 3 then v 1 + fvOccF L (v 2) else v 1) by
      simpa [blueprint, fvOccF.defined.iff]
    by_cases h : v 2 ∈ v 3
    · simp [h]
    · simp [h]

end FvOccS

variable (L)

/-- Partial sum `Σ_{p ∈ s, p < i} fvOccF p`. -/
noncomputable def fvOccSAux (s i : V) : V := (FvOccS.construction L).result ![s] i

/-- Number of free-variable occurrences in a formula-set code: `Σ_{p ∈ s} fvOccF p`. -/
noncomputable def fvOccS (s : V) : V := fvOccSAux L s s

variable {L}

@[simp] lemma fvOccSAux_zero (s : V) : fvOccSAux L s 0 = 0 := by
  simp [fvOccSAux, FvOccS.construction]

lemma fvOccSAux_succ (s i : V) :
    fvOccSAux L s (i + 1) = if i ∈ s then fvOccSAux L s i + fvOccF L i else fvOccSAux L s i := by
  simp [fvOccSAux, FvOccS.construction]

@[simp] lemma fvOccSAux_succ_of_mem {s i : V} (h : i ∈ s) :
    fvOccSAux L s (i + 1) = fvOccSAux L s i + fvOccF L i := by simp [fvOccSAux_succ, h]

@[simp] lemma fvOccSAux_succ_of_not_mem {s i : V} (h : i ∉ s) :
    fvOccSAux L s (i + 1) = fvOccSAux L s i := by simp [fvOccSAux_succ, h]

section

variable (L)

noncomputable def fvOccSAuxDef : 𝚺₁.Semisentence 3 :=
  (FvOccS.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

variable {L}

instance fvOccSAux_defined : 𝚺₁-Function₂[V] fvOccSAux L via fvOccSAuxDef L := .mk fun v ↦ by
  simp [(FvOccS.construction L).result_defined_iff, fvOccSAuxDef]; rfl

instance fvOccSAux_definable : 𝚺₁-Function₂[V] fvOccSAux L := fvOccSAux_defined.to_definable

instance fvOccSAux_definable' (Γ m) : Γ-[m + 1]-Function₂ (fvOccSAux (V := V) L) :=
  fvOccSAux_definable.of_sigmaOne

variable (L)

/-- `fvOccS` as a substitution instance of `fvOccSAuxDef` (not a `“ ”`-DSL wrapper — see the
remark at `setLenDef`). -/
noncomputable def fvOccSDef : 𝚺₁.Semisentence 2 := (fvOccSAuxDef L).rew (Rew.subst ![#0, #1, #1])

variable {L}

instance fvOccS_defined : 𝚺₁-Function₁[V] fvOccS L via fvOccSDef L := .mk fun v ↦ by
  simp [fvOccSDef, fvOccSAuxDef, (FvOccS.construction L).result_defined_iff, fvOccS]; rfl

instance fvOccS_definable : 𝚺₁-Function₁[V] fvOccS L := fvOccS_defined.to_definable

instance fvOccS_definable' (Γ m) : Γ-[m + 1]-Function₁ (fvOccS (V := V) L) :=
  fvOccS_definable.of_sigmaOne

end

/-- The partial sums stabilise once the index passes the set. -/
lemma fvOccSAux_add_eq (s j : V) : fvOccSAux L s (s + j) = fvOccS L s := by
  induction j using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp [fvOccS]
  | succ j ih =>
    have hnot : s + j ∉ s := fun hm ↦ absurd (lt_of_mem hm) (not_lt.mpr le_self_add)
    rw [← add_assoc, fvOccSAux_succ_of_not_mem hnot, ih]

lemma fvOccSAux_eq_of_le {s i : V} (h : s ≤ i) : fvOccSAux L s i = fvOccS L s := by
  obtain ⟨j, rfl⟩ := exists_add_of_le h
  exact fvOccSAux_add_eq s j

lemma fvOccSAux_insert_of_not_mem {x s : V} (hx : x ∉ s) (i : V) :
    (i ≤ x → fvOccSAux L (insert x s) i = fvOccSAux L s i) ∧
    (x < i → fvOccSAux L (insert x s) i = fvOccSAux L s i + fvOccF L x) := by
  induction i using ISigma1.sigma1_succ_induction with
  | hP => definability
  | zero => simp
  | succ i ih =>
    by_cases hix : i = x
    · subst hix
      refine ⟨fun h ↦ absurd h (not_le.mpr (lt_add_one i)), fun _ ↦ ?_⟩
      rw [fvOccSAux_succ_of_mem (mem_insert i s), fvOccSAux_succ_of_not_mem hx, ih.1 (le_refl i)]
    · have hmem : (i ∈ insert x s) ↔ i ∈ s := by simp [hix]
      constructor
      · intro hi
        have hi' : i ≤ x := le_of_lt (lt_of_lt_of_le (lt_add_one i) hi)
        by_cases his : i ∈ s
        · rw [fvOccSAux_succ_of_mem (hmem.mpr his), fvOccSAux_succ_of_mem his, ih.1 hi']
        · rw [fvOccSAux_succ_of_not_mem (fun h ↦ his (hmem.mp h)),
            fvOccSAux_succ_of_not_mem his, ih.1 hi']
      · intro hi
        have hxi : x < i := lt_of_le_of_ne (lt_succ_iff_le.mp hi) (Ne.symm hix)
        by_cases his : i ∈ s
        · rw [fvOccSAux_succ_of_mem (hmem.mpr his), fvOccSAux_succ_of_mem his, ih.2 hxi]
          exact add_right_comm _ _ _
        · rw [fvOccSAux_succ_of_not_mem (fun h ↦ his (hmem.mp h)),
            fvOccSAux_succ_of_not_mem his, ih.2 hxi]

lemma fvOccS_insert_of_not_mem {x s : V} (hx : x ∉ s) :
    fvOccS L (insert x s) = fvOccS L s + fvOccF L x := by
  have hlt : x < insert x s := lt_of_mem (by simp)
  have hle : s ≤ insert x s := le_of_subset (fun i hi ↦ by simp [hi])
  rw [fvOccS, (fvOccSAux_insert_of_not_mem hx _).2 hlt, fvOccSAux_eq_of_le hle]

/-- Inserting a formula adds at most its free-variable occurrences. -/
lemma fvOccS_insert_le (x s : V) : fvOccS L (insert x s) ≤ fvOccS L s + fvOccF L x := by
  by_cases hx : x ∈ s
  · rw [insert_eq_self_of_mem hx]; exact le_self_add
  · exact le_of_eq (fvOccS_insert_of_not_mem hx)

@[simp] lemma fvOccS_empty : fvOccS L (∅ : V) = 0 := by
  simp [fvOccS, emptyset_def]

@[simp] lemma fvOccS_singleton (x : V) : fvOccS L ({x} : V) = fvOccF L x := by
  rw [singleton_eq_insert, fvOccS_insert_of_not_mem (by simp), fvOccS_empty, zero_add]

/-- `fvOccS s ≤ setLen s` for a set of formulas. -/
lemma fvOccS_le_setLen {s : V} (hs : IsFormulaSet L s) : fvOccS L s ≤ setLen L s := by
  refine insert_induction_piOne (P := fun s ↦ IsFormulaSet L s → fvOccS L s ≤ setLen L s)
    ?_ ?_ ?_ s hs
  · definability
  · intro _; simp
  · intro a s ha ih hs
    have hs' : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp hs).2
    have ha' : IsFormula L a := (IsFormulaSet.insert_iff.mp hs).1
    rw [fvOccS_insert_of_not_mem ha, setLen_insert_of_not_mem_V ha]
    exact add_le_add (ih hs') (fvOccF_le_formulaLen ha'.isUFormula)

/-- **The additive bound for sets**: `setLen (setShift s) ≤ setLen s + fvOccS s` (`≤`: without
an injectivity lemma for `shift` on codes, `setShift` may identify two members). -/
lemma setLen_setShift_le_occ {s : V} (hs : IsFormulaSet L s) :
    setLen L (setShift L s) ≤ setLen L s + fvOccS L s := by
  refine insert_induction_piOne
    (P := fun s ↦ IsFormulaSet L s → setLen L (setShift L s) ≤ setLen L s + fvOccS L s)
    ?_ ?_ ?_ s hs
  · definability
  · intro _; simp
  · intro a s ha ih hs
    have hs' : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp hs).2
    have ha' : IsFormula L a := (IsFormulaSet.insert_iff.mp hs).1
    rw [mem_setShift_insert, setLen_insert_of_not_mem_V ha, fvOccS_insert_of_not_mem ha]
    calc setLen L (insert (shift L a) (setShift L s))
        ≤ setLen L (setShift L s) + formulaLen L (shift L a) := setLen_insert_le _ _
      _ ≤ (setLen L s + fvOccS L s) + (formulaLen L a + fvOccF L a) :=
          add_le_add (ih hs') (le_of_eq (formulaLen_shift_eq ha'.isUFormula))
      _ = setLen L s + formulaLen L a + (fvOccS L s + fvOccF L a) := by ring

/-- `setShift` does not increase the number of free-variable occurrences (`=` would need
injectivity of `shift`). -/
lemma fvOccS_setShift_le {s : V} (hs : IsFormulaSet L s) : fvOccS L (setShift L s) ≤ fvOccS L s := by
  refine insert_induction_piOne
    (P := fun s ↦ IsFormulaSet L s → fvOccS L (setShift L s) ≤ fvOccS L s) ?_ ?_ ?_ s hs
  · definability
  · intro _; simp
  · intro a s ha ih hs
    have hs' : IsFormulaSet L s := (IsFormulaSet.insert_iff.mp hs).2
    have ha' : IsFormula L a := (IsFormulaSet.insert_iff.mp hs).1
    rw [mem_setShift_insert, fvOccS_insert_of_not_mem ha]
    exact le_trans (fvOccS_insert_le _ _)
      (add_le_add (ih hs') (le_of_eq (fvOccF_shift ha'.isUFormula)))

/-! #### Iterated shifts cost linearly -/

variable (L) in
/-- `n` applications of `setShift`. -/
noncomputable def setShiftIter : ℕ → V → V
  | 0, s => s
  | n + 1, s => setShift L (setShiftIter n s)

@[simp] lemma setShiftIter_zero (s : V) : setShiftIter L 0 s = s := rfl
@[simp] lemma setShiftIter_succ (n : ℕ) (s : V) :
    setShiftIter L (n + 1) s = setShift L (setShiftIter L n s) := rfl

lemma isFormulaSet_setShiftIter {n : ℕ} {s : V} (hs : IsFormulaSet L s) :
    IsFormulaSet L (setShiftIter L n s) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact ih.setShift

lemma fvOccS_setShiftIter_le {n : ℕ} {s : V} (hs : IsFormulaSet L s) :
    fvOccS L (setShiftIter L n s) ≤ fvOccS L s := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (fvOccS_setShift_le (isFormulaSet_setShiftIter hs)) ih

/-- **`n` shifts cost `n · fvOccS s`**, not `2ⁿ · setLen s`:
`setLen (setShift^[n] s) ≤ setLen s + n · fvOccS s`. -/
theorem setLen_setShiftIter_le {n : ℕ} {s : V} (hs : IsFormulaSet L s) :
    setLen L (setShiftIter L n s) ≤ setLen L s + (n : V) * fvOccS L s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [setShiftIter_succ, Nat.cast_succ, add_mul, one_mul, ← add_assoc]
    exact le_trans (setLen_setShift_le_occ (isFormulaSet_setShiftIter hs))
      (add_le_add ih (fvOccS_setShiftIter_le hs))

end set

/-! ### The consequence for `elimExistsCode` -/

section elim

variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]

/-- **The bound for `elimExistsCode` with the additive shift term**
(`dlen_elimExistsCode_le` + `setLen_setShift_le_occ`):
`dlen ≤ dlen D + dlen d + 4·|Γ| + fvOccS Γ + 6|P| + 8` — the `5·|Γ|` of
`dlen_elimExistsCode_le'` had the doubled context `|setShift Γ| ≤ 2|Γ|` in it. -/
theorem dlen_elimExistsCode_le_occ {Γ Δ P D d : V} (hP : IsSemiformula L 1 P) (hΓ : IsFormulaSet L Γ)
    (hΔ : Δ ⊆ Γ) (hD : DerivationOf T D (insert (^∃ P) Δ))
    (hd : DerivationOf T d (insert (neg L (free L P)) (setShift L Γ))) :
    dlen T (elimExistsCode L Γ P D d) ≤
      dlen T D + dlen T d + 4 * setLen L Γ + fvOccS L Γ + 6 * formulaLen L P + 8 := by
  refine le_trans (dlen_elimExistsCode_le hP hΓ hΔ hD hd) ?_
  have := setLen_setShift_le_occ hΓ
  calc dlen T D + dlen T d + 3 * setLen L Γ + setLen L (setShift L Γ) + 6 * formulaLen L P + 8
      ≤ dlen T D + dlen T d + 3 * setLen L Γ + (setLen L Γ + fvOccS L Γ) + 6 * formulaLen L P + 8 := by
        gcongr
    _ = dlen T D + dlen T d + 4 * setLen L Γ + fvOccS L Γ + 6 * formulaLen L P + 8 := by ring

end elim

end ArithS

import Foundation.FirstOrder.Incompleteness.RestrictedProvability

/-!
# ArithS.Length — the structural symbol count on Foundation's term and formula codes

Milestone M1 of `ARITHMETIZED_S_ROADMAP.md`, part 1 (terms and formulas; sequents and
derivations follow in `ArithS.DerivationLength`).

`len` is Critch's "characters of text" made precise on Foundation's HFS codes: the number
of symbols of the decoded syntax tree. Two design commitments (roadmap §2.1):

* it is STRUCTURAL — a function symbol or relation symbol counts `1` whatever its code, so
  swapping two constant symbols (the τ-transposition of §2.4) preserves it exactly;
* variable indices are charged unary (`z + 1`, `x + 1`), matching Foundation's unary
  numerals (`Semiterm.Operator.numeral`, `1 + ⋯ + 1`). Critch's assumption (b) — a number
  `k` in `O(lg k)` characters — is therefore NOT met by the raw ℒₒᵣ coding; that is a
  cost-faithfulness item for tier T3, irrelevant to T1/T2, recorded in the roadmap.

Templates: `listMax` (`HFS/Vec.lean`), `termBV` (`Bootstrapping/Syntax/Term/Basic.lean`),
`bv` (`Bootstrapping/Syntax/Formula/Basic.lean`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Sum of a list -/

namespace ListSum

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. y = x + ih”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := x + ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]

end ListSum

noncomputable def listSum (v : V) : V := ListSum.construction.result ![] v

@[simp] lemma listSum_nil : listSum (0 : V) = 0 := by simp [listSum, ListSum.construction]

@[simp] lemma listSum_adjoin (x v : V) : listSum (x ∷ v) = x + listSum v := by
  simp [listSum, ListSum.construction]

def listSumDef : 𝚺₁.Semisentence 2 := ListSum.blueprint.resultDef

instance listSum_defined : 𝚺₁-Function₁ (listSum : V → V) via listSumDef :=
  ListSum.construction.result_defined

instance listSum_definable : 𝚺₁-Function₁ (listSum : V → V) := listSum_defined.to_definable

instance listSum_definable' (Γ m) : Γ-[m + 1]-Function₁ (listSum : V → V) :=
  listSum_definable.of_sigmaOne

/-! ### Terms -/

section term

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace TermLen

def blueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = z + 1”
  fvar := .mkSigma “y x. y = x + 1”
  func := .mkSigma “y k f v v'. ∃ s, !listSumDef s v' ∧ y = s + 1”

variable (L)

noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z)        := z + 1
  fvar (_ x)        := x + 1
  func (_ _ _ _ v') := listSum v' + 1
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]

end TermLen

open TermLen

variable (L)

/-- Symbol count of a term code: a symbol counts `1`, a variable index `i` counts `i + 1`. -/
noncomputable def termLen (t : V) : V := (construction L).result L ![] t

noncomputable def termLenVec (k v : V) : V := (construction L).resultVec L ![] k v

noncomputable def termLenGraph : 𝚺₁.Semisentence 2 := blueprint.result L

noncomputable def termLenVecGraph : 𝚺₁.Semisentence 3 := blueprint.resultVec L

variable {L}

@[simp] lemma termLen_bvar (z : V) : termLen L ^#z = z + 1 := by simp [termLen, construction]

@[simp] lemma termLen_fvar (x : V) : termLen L ^&x = x + 1 := by simp [termLen, construction]

@[simp] lemma termLen_func {k f v : V} (hkf : L.IsFunc k f) (hv : IsUTermVec L k v) :
    termLen L (^func k f v) = listSum (termLenVec L k v) + 1 := by
  simp [termLen, construction, hkf, hv]; rfl

@[simp] lemma len_termLenVec {k v : V} (hv : IsUTermVec L k v) :
    len (termLenVec L k v) = k := (construction L).resultVec_lh L _ hv

@[simp] lemma nth_termLenVec {k v : V} (hv : IsUTermVec L k v) {i} (hi : i < k) :
    (termLenVec L k v).[i] = termLen L v.[i] := (construction L).nth_resultVec L _ hv hi

@[simp] lemma termLenVec_nil : termLenVec L 0 0 = 0 := (construction L).resultVec_nil L _

lemma termLenVec_cons {k t ts : V} (ht : IsUTerm L t) (hts : IsUTermVec L k ts) :
    termLenVec L (k + 1) (t ∷ ts) = termLen L t ∷ termLenVec L k ts :=
  (construction L).resultVec_cons L ![] hts ht

instance termLen.defined : 𝚺₁-Function₁ (termLen (V := V) L) via (termLenGraph L) :=
  (construction L).result_defined

instance termLen.definable : 𝚺₁-Function₁ (termLen (V := V) L) := termLen.defined.to_definable

instance termLen.definable' : Γ-[k + 1]-Function₁ (termLen (V := V) L) :=
  termLen.definable.of_sigmaOne

instance termLenVec.defined : 𝚺₁-Function₂ (termLenVec (V := V) L) via (termLenVecGraph L) :=
  (construction L).resultVec_defined

instance termLenVec.definable : 𝚺₁-Function₂ (termLenVec (V := V) L) :=
  termLenVec.defined.to_definable

instance termLenVec.definable' : Γ-[i + 1]-Function₂ (termLenVec (V := V) L) :=
  termLenVec.definable.of_sigmaOne

end term

/-! ### Formulas -/

section formula

variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace FormulaLen

variable (L)

noncomputable def blueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ M, !(termLenVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s + 1”
  nrel := .mkSigma “y param k R v. ∃ M, !(termLenVecGraph L) M k v ∧ ∃ s, !listSumDef s M ∧ y = s + 1”
  verum := .mkSigma “y param. y = 1”
  falsum := .mkSigma “y param. y = 1”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂ + 1”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. y = y₁ + y₂ + 1”
  all := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  exs := .mkSigma “y param p₁ y₁. y = y₁ + 1”
  allChanges := .mkSigma “param' param. param' = 0”
  exsChanges := .mkSigma “param' param. param' = 0”

noncomputable def construction : UformulaRec1.Construction V (blueprint L) where
  rel {_} := fun k _ v ↦ listSum (termLenVec L k v) + 1
  nrel {_} := fun k _ v ↦ listSum (termLenVec L k v) + 1
  verum {_} := 1
  falsum {_} := 1
  and {_} := fun _ _ y₁ y₂ ↦ y₁ + y₂ + 1
  or {_} := fun _ _ y₁ y₂ ↦ y₁ + y₂ + 1
  all {_} := fun _ y₁ ↦ y₁ + 1
  exs {_} := fun _ y₁ ↦ y₁ + 1
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

end FormulaLen

open FormulaLen

variable (L)

/-- Symbol count of a formula code. -/
noncomputable def formulaLen (p : V) : V := (FormulaLen.construction L).result L 0 p

noncomputable def formulaLenGraph : 𝚺₁.Semisentence 2 :=
  ((FormulaLen.blueprint L).result L).rew (Rew.subst ![#0, ‘0’, #1])

variable {L}

instance formulaLen.defined : 𝚺₁-Function₁ formulaLen (V := V) L via formulaLenGraph L := .mk fun v ↦ by
  simpa [formulaLenGraph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
    using! (FormulaLen.construction L).result_defined.defined ![v 0, 0, v 1]

instance formulaLen.definable : 𝚺₁-Function₁ formulaLen (V := V) L := formulaLen.defined.to_definable

instance formulaLen.definable' : Γ-[m + 1]-Function₁ formulaLen (V := V) L :=
  formulaLen.definable.of_sigmaOne

@[simp] lemma formulaLen_rel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaLen L (^rel k R v) = listSum (termLenVec L k v) + 1 := by
  simp [formulaLen, hR, hv, FormulaLen.construction]

@[simp] lemma formulaLen_nrel {k R v : V} (hR : L.IsRel k R) (hv : IsUTermVec L k v) :
    formulaLen L (^nrel k R v) = listSum (termLenVec L k v) + 1 := by
  simp [formulaLen, hR, hv, FormulaLen.construction]

@[simp] lemma formulaLen_verum : formulaLen L (^⊤ : V) = 1 := by
  simp [formulaLen, FormulaLen.construction]

@[simp] lemma formulaLen_falsum : formulaLen L (^⊥ : V) = 1 := by
  simp [formulaLen, FormulaLen.construction]

@[simp] lemma formulaLen_and {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaLen L (p ^⋏ q) = formulaLen L p + formulaLen L q + 1 := by
  simp [formulaLen, hp, hq, FormulaLen.construction]

@[simp] lemma formulaLen_or {p q : V} (hp : IsUFormula L p) (hq : IsUFormula L q) :
    formulaLen L (p ^⋎ q) = formulaLen L p + formulaLen L q + 1 := by
  simp [formulaLen, hp, hq, FormulaLen.construction]

@[simp] lemma formulaLen_all {p : V} (hp : IsUFormula L p) :
    formulaLen L (^∀ p) = formulaLen L p + 1 := by
  simp [formulaLen, hp, FormulaLen.construction]

@[simp] lemma formulaLen_exs {p : V} (hp : IsUFormula L p) :
    formulaLen L (^∃ p) = formulaLen L p + 1 := by
  simp [formulaLen, hp, FormulaLen.construction]

end formula

end ArithS

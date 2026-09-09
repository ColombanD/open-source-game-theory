import ArithS.Length

/-!
# ArithS.SequentLength — symbol count of a sequent (an HFS bit-set of formula codes)

`setLen s = Σ_{p ∈ s} formulaLen p`, by primitive recursion over the indices `i < s`
(every member of a bit-set is below the set: `lt_of_mem`). Needed because the weakening
rule introduces arbitrary formulas, so a proper length measure must charge the target
sequent there (roadmap §2.1, PROPER).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open Classical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace SetLen

variable (L)

/-- `zero s = 0`; `succ s i ih = ih + formulaLen i` if `i ∈ s`, else `ih`. -/
noncomputable def blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y s. y = 0”
  succ := .mkSigma “y ih i s. (i ∈ s → ∃ l, !(formulaLenGraph L) l i ∧ y = ih + l) ∧ (¬i ∈ s → y = ih)”

noncomputable def construction : PR.Construction V (blueprint L) where
  zero := fun _ ↦ 0
  succ := fun v i ih ↦ if i ∈ v 0 then ih + formulaLen L i else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    suffices
      (v 2 ∈ v 3 → v 0 = v 1 + formulaLen L (v 2)) ∧ (v 2 ∉ v 3 → v 0 = v 1) ↔
      (v 0 = if v 2 ∈ v 3 then v 1 + formulaLen L (v 2) else v 1) by
      simpa [blueprint, formulaLen.defined.iff]
    by_cases h : v 2 ∈ v 3
    · simp [h]
    · simp [h]

end SetLen

variable (L)

/-- Partial sum `Σ_{p ∈ s, p < i} formulaLen p`. -/
noncomputable def setLenAux (s i : V) : V := (SetLen.construction L).result ![s] i

/-- Symbol count of a sequent: `Σ_{p ∈ s} formulaLen p`. -/
noncomputable def setLen (s : V) : V := setLenAux L s s

variable {L}

@[simp] lemma setLenAux_zero (s : V) : setLenAux L s 0 = 0 := by
  simp [setLenAux, SetLen.construction]

lemma setLenAux_succ (s i : V) :
    setLenAux L s (i + 1) = if i ∈ s then setLenAux L s i + formulaLen L i else setLenAux L s i := by
  simp [setLenAux, SetLen.construction]

@[simp] lemma setLenAux_succ_of_mem {s i : V} (h : i ∈ s) :
    setLenAux L s (i + 1) = setLenAux L s i + formulaLen L i := by simp [setLenAux_succ, h]

@[simp] lemma setLenAux_succ_of_not_mem {s i : V} (h : i ∉ s) :
    setLenAux L s (i + 1) = setLenAux L s i := by simp [setLenAux_succ, h]

section

variable (L)

noncomputable def setLenAuxDef : 𝚺₁.Semisentence 3 :=
  (SetLen.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

variable {L}

instance setLenAux_defined : 𝚺₁-Function₂[V] setLenAux L via setLenAuxDef L := .mk fun v ↦ by
  simp [(SetLen.construction L).result_defined_iff, setLenAuxDef]; rfl

instance setLenAux_definable : 𝚺₁-Function₂[V] setLenAux L := setLenAux_defined.to_definable

instance setLenAux_definable' (Γ m) : Γ-[m + 1]-Function₂ (setLenAux (V := V) L) :=
  setLenAux_definable.of_sigmaOne

variable (L)

/-- `setLen` as a substitution instance of `setLenAuxDef` (NOT a `“ ”`-DSL wrapper: simp on
the wrapper form normalizes the substitution through the whole PR `resultDef` and runs
away — 17 GB, never terminates). -/
noncomputable def setLenDef : 𝚺₁.Semisentence 2 := (setLenAuxDef L).rew (Rew.subst ![#0, #1, #1])

variable {L}

instance setLen_defined : 𝚺₁-Function₁[V] setLen L via setLenDef L := .mk fun v ↦ by
  simp [setLenDef, setLenAuxDef, (SetLen.construction L).result_defined_iff, setLen]; rfl

instance setLen_definable : 𝚺₁-Function₁[V] setLen L := setLen_defined.to_definable

instance setLen_definable' (Γ m) : Γ-[m + 1]-Function₁ (setLen (V := V) L) :=
  setLen_definable.of_sigmaOne

end

end ArithS

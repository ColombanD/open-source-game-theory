import ArithS.Length.Length

/-!
# ArithS.SequentLength — symbol count of a sequent (an HFS bit-set of formula codes)

`sequentLen s = Σ_{p ∈ s} formulaLen p`, by primitive recursion over the indices `i < s`
(every member of a bit-set is below the set: `lt_of_mem`). Needed because the weakening
rule introduces arbitrary formulas, so a proper length measure must charge the target
sequent there (roadmap §2.1, PROPER).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open Classical

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

namespace SequentLen

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

end SequentLen

variable (L)

/-- Partial sum `Σ_{p ∈ s, p < i} formulaLen p`. -/
noncomputable def sequentLenAux (s i : V) : V := (SequentLen.construction L).result ![s] i

/-- Symbol count of a sequent: `Σ_{p ∈ s} formulaLen p`. -/
noncomputable def sequentLen (s : V) : V := sequentLenAux L s s

variable {L}

@[simp] lemma sequentLenAux_zero (s : V) : sequentLenAux L s 0 = 0 := by
  simp [sequentLenAux, SequentLen.construction]

lemma sequentLenAux_succ (s i : V) :
    sequentLenAux L s (i + 1) = if i ∈ s then sequentLenAux L s i + formulaLen L i else sequentLenAux L s i := by
  simp [sequentLenAux, SequentLen.construction]

@[simp] lemma sequentLenAux_succ_of_mem {s i : V} (h : i ∈ s) :
    sequentLenAux L s (i + 1) = sequentLenAux L s i + formulaLen L i := by simp [sequentLenAux_succ, h]

@[simp] lemma sequentLenAux_succ_of_not_mem {s i : V} (h : i ∉ s) :
    sequentLenAux L s (i + 1) = sequentLenAux L s i := by simp [sequentLenAux_succ, h]

section

variable (L)

noncomputable def sequentLenAuxDef : 𝚺₁.Semisentence 3 :=
  (SequentLen.blueprint L).resultDef |>.rew (Rew.subst ![#0, #2, #1])

variable {L}

instance sequentLenAux_defined : 𝚺₁-Function₂[V] sequentLenAux L via sequentLenAuxDef L := .mk fun v ↦ by
  simp [(SequentLen.construction L).result_defined_iff, sequentLenAuxDef]; rfl

instance sequentLenAux_definable : 𝚺₁-Function₂[V] sequentLenAux L := sequentLenAux_defined.to_definable

instance sequentLenAux_definable' (Γ m) : Γ-[m + 1]-Function₂ (sequentLenAux (V := V) L) :=
  sequentLenAux_definable.of_sigmaOne

variable (L)

/-- `sequentLen` as a substitution instance of `sequentLenAuxDef` (NOT a `“ ”`-DSL wrapper: simp on
the wrapper form normalizes the substitution through the whole PR `resultDef` and runs
away — 17 GB, never terminates). -/
noncomputable def sequentLenDef : 𝚺₁.Semisentence 2 := (sequentLenAuxDef L).rew (Rew.subst ![#0, #1, #1])

variable {L}

instance sequentLen_defined : 𝚺₁-Function₁[V] sequentLen L via sequentLenDef L := .mk fun v ↦ by
  simp [sequentLenDef, sequentLenAuxDef, (SequentLen.construction L).result_defined_iff, sequentLen]; rfl

instance sequentLen_definable : 𝚺₁-Function₁[V] sequentLen L := sequentLen_defined.to_definable

instance sequentLen_definable' (Γ m) : Γ-[m + 1]-Function₁ (sequentLen (V := V) L) :=
  sequentLen_definable.of_sigmaOne

end

end ArithS

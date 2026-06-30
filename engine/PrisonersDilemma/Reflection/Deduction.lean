import PrisonersDilemma.Reflection.Proves

/-!
# Reflection layer — the deduction theorem `impI` for the object system (E5 prerequisite)

`BPSb.impI : (Proves p → Proves q) → Proves (p → q)` is the one field the base `Proves` lacks. The
`ImpIFeasibilitySpike` showed the right route: a hypothesis-extended `ProvesH Γ` with a DERIVED
deduction theorem (admissible meta-theorem from S/K/mp), NOT an unsound primitive.

This module adds `ProvesH` over the real `OFml`, proves `deduction`, and bridges it to the base
`Proves` (`ProvesH [] φ ↔ Proves φ`) — so `Reflection/Bpsb.lean` can supply `impI` for the BPSb
instance without disturbing the landed E1–E4 modules. NOT yet root-imported.
-/

namespace PD.Reflection

/-! ## 1. Hypothesis-extended provability `ProvesH Γ φ`.

Mirrors `Proves`' rules with an assumption list `Γ`, plus `hyp`. The HBL rules and `gammaAx`/
`betaGamma` are closed axioms (hold in any `Γ`); `nec` is context-free (closed-theorem necessitation,
the standard side-condition). Just enough to reproduce `Proves` and prove `deduction`. -/

inductive ProvesH : List OFml → OFml → Prop where
  | hyp     {Γ : List OFml} {a : OFml} : a ∈ Γ → ProvesH Γ a
  | impId   (Γ : List OFml) (a : OFml) : ProvesH Γ (.imp a a)
  | impK    (Γ : List OFml) (a b : OFml) : ProvesH Γ (.imp a (.imp b a))
  | impS    (Γ : List OFml) (a b c : OFml) :
      ProvesH Γ (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | mp {Γ : List OFml} {a b : OFml} : ProvesH Γ (.imp a b) → ProvesH Γ a → ProvesH Γ b
  -- `iff` rules, present only so closed `Proves` facts (e.g. the `diag`/`repr` legs) lift into a
  -- context; the deduction theorem never DISCHARGES an `iff` (the chain splits it first), so these
  -- arms are handled by weakening in `deduction`.
  | iffIntro {Γ : List OFml} {a b : OFml} :
      ProvesH [] (.imp a b) → ProvesH [] (.imp b a) → ProvesH Γ (.iff a b)
  | iffMPF {Γ : List OFml} {a b : OFml} : ProvesH [] (.iff a b) → ProvesH Γ (.imp a b)
  | iffMPB {Γ : List OFml} {a b : OFml} : ProvesH [] (.iff a b) → ProvesH Γ (.imp b a)
  | D2_K    (Γ : List OFml) (a b : OFml) :
      ProvesH Γ (.imp (.box (.imp a b)) (.imp (.box a) (.box b)))
  | D3_four (Γ : List OFml) (a : OFml) : ProvesH Γ (.imp (.box a) (.box (.box a)))
  | nec {Γ : List OFml} {a : OFml} : ProvesH [] a → ProvesH Γ (.box a)
  | gammaAx (Γ : List OFml) (n : Nat) : ProvesH Γ (.gamma n (e n))
  | betaGamma (Γ : List OFml) (n y : Nat) :
      ProvesH Γ (.imp (.gamma n y) (.iff (.betaA n) (.gApp y)))

/-! ## 2. Weakening + the deduction theorem (`impI`). -/

theorem weakenH {Γ Δ : List OFml} {a : OFml} (hsub : Γ ⊆ Δ) (h : ProvesH Γ a) : ProvesH Δ a := by
  induction h generalizing Δ with
  | hyp hmem => exact ProvesH.hyp (hsub hmem)
  | impId _ a => exact ProvesH.impId _ a
  | impK _ a b => exact ProvesH.impK _ a b
  | impS _ a b c => exact ProvesH.impS _ a b c
  | mp _ _ ihab iha => exact ProvesH.mp (ihab hsub) (iha hsub)
  | iffIntro hab hba _ _ => exact ProvesH.iffIntro hab hba
  | iffMPF h _ => exact ProvesH.iffMPF h
  | iffMPB h _ => exact ProvesH.iffMPB h
  | D2_K _ a b => exact ProvesH.D2_K _ a b
  | D3_four _ a => exact ProvesH.D3_four _ a
  | nec h _ => exact ProvesH.nec h
  | gammaAx _ n => exact ProvesH.gammaAx _ n
  | betaGamma _ n y => exact ProvesH.betaGamma _ n y

/-- **The deduction theorem = `impI`** — `ProvesH (p :: Γ) q → ProvesH Γ (.imp p q)`. Admissible
    meta-theorem (S/K/mp), so `impI` carries NO new axiom and no soundness risk. -/
theorem deduction {Γ : List OFml} {p q : OFml} (h : ProvesH (p :: Γ) q) :
    ProvesH Γ (.imp p q) := by
  generalize hΓ : (p :: Γ) = Γ' at h
  induction h generalizing Γ with
  | @hyp Γ' a hmem =>
      subst hΓ
      rcases List.mem_cons.mp hmem with h | h
      · subst h; exact ProvesH.impId Γ a
      · exact ProvesH.mp (ProvesH.impK Γ a p) (ProvesH.hyp h)
  | impId Γ' a => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impId _ _)
  | impK Γ' a b => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impK _ _ _)
  | impS Γ' a b c => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.impS _ _ _ _)
  | @mp Γ' a b _ _ ihab iha =>
      subst hΓ
      exact ProvesH.mp (ProvesH.mp (ProvesH.impS _ p a b) (ihab rfl)) (iha rfl)
  -- iff conclusions are closed theorems (premises on []); re-derive then weaken via impK.
  | iffIntro hab hba _ _ => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.iffIntro hab hba)
  | iffMPF h _ => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.iffMPF h)
  | iffMPB h _ => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.iffMPB h)
  | D2_K Γ' a b => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.D2_K _ _ _)
  | D3_four Γ' a => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.D3_four _ _)
  | @nec Γ' a h _ => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.nec h)
  | gammaAx Γ' n => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.gammaAx _ _)
  | betaGamma Γ' n y => subst hΓ; exact ProvesH.mp (ProvesH.impK _ _ _) (ProvesH.betaGamma _ _ _)

/-! ## 3. Bridge `ProvesH [] φ ↔ Proves φ` — so `impI` lands in the base system.

The forward map sends each closed `ProvesH` rule to its `Proves` counterpart. The backward map is the
obvious embedding. We need the forward direction for the `BPSb` instance (whose `Proves` field is the
base `Proves`). -/

/-- Forward map for ANY context: a `ProvesH Γ φ` becomes a base `Proves φ` once we discharge the
    hypotheses. We only need the closed case (`Γ = []`); state it generally over the rules and read off
    `[]` at the call site. Here `nec`'s premise is already closed, so its `ih` is directly the base
    proof — no manual recursion, the structural `induction` handles termination. -/
theorem proves_of_provesH_aux {Γ : List OFml} {φ : OFml}
    (hclosed : ∀ a ∈ Γ, Proves a) (h : ProvesH Γ φ) : Proves φ := by
  induction h with
  | hyp hmem => exact hclosed _ hmem
  | impId _ a => exact Proves.impId a
  | impK _ a b => exact Proves.impK a b
  | impS _ a b c => exact Proves.impS a b c
  | mp _ _ ihab iha => exact Proves.mp (ihab hclosed) (iha hclosed)
  | iffIntro _ _ ihab ihba => exact Proves.iffIntro (ihab (by simp)) (ihba (by simp))
  | iffMPF _ ih => exact Proves.iffMPF (ih (by simp))
  | iffMPB _ ih => exact Proves.iffMPB (ih (by simp))
  | D2_K _ a b => exact Proves.D2_K a b
  | D3_four _ a => exact Proves.D3_four a
  | nec h ih => exact Proves.D1_nec (ih (by simp))
  | gammaAx _ n => exact Proves.gammaAx n
  | betaGamma _ n y => exact Proves.betaGamma n y

theorem proves_of_provesH {φ : OFml} (h : ProvesH [] φ) : Proves φ :=
  proves_of_provesH_aux (by simp) h

/-- Lift a closed base theorem into any context — `Proves φ → ProvesH Γ φ`. Structural copy (the
    object rules all have `ProvesH` counterparts). Needed to feed `Proves` facts (the chain's `hnec`/
    `hA`/`hLoeb`) into a hypothesis-derivation. -/
theorem provesH_of_proves {φ : OFml} (h : Proves φ) : ProvesH [] φ := by
  induction h with
  | impId a => exact ProvesH.impId _ a
  | mp _ _ ihab iha => exact ProvesH.mp ihab iha
  | impK a b => exact ProvesH.impK _ a b
  | impS a b c => exact ProvesH.impS _ a b c
  | iffIntro _ _ ihab ihba => exact ProvesH.iffIntro ihab ihba
  | iffMPF _ ih => exact ProvesH.iffMPF ih
  | iffMPB _ ih => exact ProvesH.iffMPB ih
  | D1_nec _ ih => exact ProvesH.nec ih
  | D2_K a b => exact ProvesH.D2_K _ a b
  | D3_four a => exact ProvesH.D3_four _ a
  | gammaAx n => exact ProvesH.gammaAx _ n
  | betaGamma n y => exact ProvesH.betaGamma _ n y

/-- Lift a closed base theorem into ANY context via weakening (`[]`-derivation + `weakenH`). -/
theorem provesH_lift {Γ : List OFml} {φ : OFml} (h : Proves φ) : ProvesH Γ φ :=
  weakenH (List.nil_subset Γ) (provesH_of_proves h)

/-- **`impI` for the base `Proves`** — from a hypothesis-derivation `ProvesH [p] q`, `deduction` gives
    `ProvesH [] (p→q)` and the bridge `proves_of_provesH` lands it in the base `Proves`. SOUND
    (`deduction` is admissible, no new axiom). This is the `BPSb.impI` field.

    Note: the `BPSb` chain only needs `impI` to discharge a SINGLE box hypothesis (`□ψ`), and it builds
    the body from `mp`/`K`/`four`/`nec` — all reproduced in `ProvesH`. The `diag` leg (an `iff`) is
    consumed via its `imp` directions OUTSIDE any hypothesis context, so `ProvesH` needs no `iff`. -/
theorem impI_base {p q : OFml} (hf : ProvesH [p] q) : Proves (.imp p q) :=
  proves_of_provesH (deduction hf)

end PD.Reflection

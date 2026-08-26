import PrisonersDilemma.Tau.Zoo

/-!
# The canonical tau ROW statement

The tau analogue of `Outcome/Spec.lean`. A tau bot's whole per-hypothesis content is its
bit row — what its compiled instance plays at every hypothesis of the zoo — and that row
is what the app's Def 3 ≡ Def 4 certification reads. Every `Tau/Theorems/<Bot>/Phase.lean`
states its row as `RowSpec …`, tagged `@[tau_row]`; `Tau/Lint.lean` validates it and
`lake exe export_outcomes` writes the bits to `app/generated/tau_rows.json`.

Before this the app regex-scanned a literal 16-entry `VoteBits` list out of the source,
and could not see that the scanned theorem was CONDITIONAL on Löb-gated hypotheses
(`hquine : proofSearch k (probe …) = true`, …) discharged only in the phase theorem.
`RowSpec` is unconditional at large `k` — the floors and the Löb gates are inside.

**This module deliberately does NOT `import Lean`**; the attribute lives in
`Outcome/Attr.lean`, the linter in `Tau/Lint.lean`.
-/

namespace PD.Tau

/-- **THE tau row template**: at every sufficiently large budget, template `A`'s
    compiled instance at each hypothesis `T ∈ order` plays `row T`. This is exactly the
    premise `vecOf_bits` and `phase_of_bits` consume, so the `VoteBits` row and the
    phase theorem are corollaries (`RowSpec.bits`). `order` is `tauOrder`, or
    `tauOrderInit` for a template whose own diagonal diverges. -/
abbrev RowSpec (A : Tmpl) (order : List Tmpl) (row : Tmpl → Action) : Prop :=
  ∃ k₂, ∀ k, k₂ < k → ∀ T ∈ order,
    ∃ N, eval N (.bot (inst (tauZoo k) A T)) (.bot (inst (tauZoo k) A T))
      (inst (tauZoo k) A T) = some (row T)

/-- The `VoteBits` reading of a row — the former scanner-facing statement, now derived. -/
theorem RowSpec.bits {A : Tmpl} {order : List Tmpl} {row : Tmpl → Action}
    (h : RowSpec A order row) :
    ∃ k₂, ∀ k, k₂ < k → ∀ w : Tmpl → Nat,
      VoteBits (vecOf (tauZoo k) A w order) (order.map fun T => (w T, row T)) := by
  obtain ⟨k₂, h⟩ := h
  exact ⟨k₂, fun k hk w => vecOf_bits (tauZoo k) A w row order (h k hk)⟩

end PD.Tau

import PrisonersDilemma.Outcome.Spec
import PrisonersDilemma.Outcome.Attr

/-!
# Outcome-theorem umbrella

The statement template plus the `@[outcome]` attribute — everything a theorem file needs.
Most files get this transitively via `Base/Helpers.lean`; the handful that do not import
`Base/Helpers` import this directly.
-/

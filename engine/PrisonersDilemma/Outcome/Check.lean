import PrisonersDilemma
import PrisonersDilemma.Outcome.Lint
import PrisonersDilemma.Tau.Lint

/-!
# The build-time outcome check

Its own lake library root, NOT part of the root `PrisonersDilemma.lean` index: the app's
`library_writer` appends `import` lines to that index, and Lean requires imports to precede
commands, so a command there would break the first LLM-written theorem that lands.

`lake build` builds this target, so the census and validator run on every build and in CI.
-/

-- The durable invariant: EVERY declaration named like a matrix cell
-- (`(llm_)outcome_<Left>_vs_<Right>`, both bot directories) is `@[outcome]`-tagged. A
-- forgotten tag is a build failure rather than a silently missing matrix cell.
#check_outcome_theorems "PrisonersDilemma/Theorems"

-- The tau twin: every `Tmpl` constructor has exactly one `@[tau_row]` row on the
-- `RowSpec` template (`Tau/RowSpec.lean`).
#check_tau_rows

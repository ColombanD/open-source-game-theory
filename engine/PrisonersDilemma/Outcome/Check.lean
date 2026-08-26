import PrisonersDilemma
import PrisonersDilemma.Outcome.Lint

/-!
# The build-time outcome check

Its own lake library root, NOT part of the root `PrisonersDilemma.lean` index: the app's
`library_writer` appends `import` lines to that index, and Lean requires imports to precede
commands, so a command there would break the first LLM-written theorem that lands.

`lake build` builds this target, so the census and validator run on every build and in CI.
-/

-- `pending 0` is the durable invariant: EVERY `outcome_X_vs_Y` declaration on disk is
-- either `@[outcome]`-tagged or listed in the exclusions file. A forgotten tag is a
-- build failure rather than a silently missing matrix cell.
--
-- The optional `expecting <n>` clause is deliberately omitted. It was the migration
-- counter, and pinning the tagged count is now a maintenance tax: proving a new outcome
-- theorem and tagging it CORRECTLY would turn the build red until someone edited a
-- literal. Re-add it only to freeze the matrix size on purpose.
#check_outcome_theorems "PrisonersDilemma/Theorems"
  excluding "PrisonersDilemma/Outcome/exclusions.txt"
  pending 0

import PrisonersDilemma
import PrisonersDilemma.Outcome.Lint

/-!
# The build-time outcome check

Its own lake library root, NOT part of the root `PrisonersDilemma.lean` index: the app's
`library_writer` appends `import` lines to that index, and Lean requires imports to precede
commands, so a command there would break the first LLM-written theorem that lands.

`lake build` builds this target, so the census and validator run on every build and in CI.
-/

-- `pending` is the migration counter: it may only ever go DOWN, and reaching 0 means
-- every outcome theorem is on-template. Until then an untagged theorem is tolerated but
-- the COUNT is pinned, so nothing new slips in untagged.
#check_outcome_theorems "PrisonersDilemma/Theorems"
  excluding "PrisonersDilemma/Outcome/exclusions.txt"
  expecting 112 pending 42

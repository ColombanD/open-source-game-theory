import PrisonersDilemma.Pipeline -- Import generic game pipeline definitions and claim predicates.

/-!
# Proof Workflow Template

Use this file as a pattern when adding a new program family.

1. Define a program type in `PrisonersDilemma/Models/<Family>.lean`.
2. Provide `ProgramModel` semantics (`SourceType`, `source`, and `actionFromSource`).
3. Create theorem files in `PrisonersDilemma/Proofs/` that prove
  `ActionClaim` first.
4. Add `OutcomeClaim` only when you actually need payoff fields.

Action-first reasoning keeps proofs small and readable:
- Stage A (default): prove what each side does.
- Stage B (optional): derive payoffs/outcomes from the payoff matrix.
-/

namespace PD.Proofs -- Reusable proof patterns and concrete theorem files.

open PD -- Bring the pipeline names into local scope.

section GenericTemplate -- Generic section for any program type with a `ProgramModel`.

variable {Prog : Type} [ProgramModel Prog] -- Abstract program language and its semantics.
variable (m : PayoffMatrix) -- Payoff matrix used for the outcome example.
variable (left right : Prog) -- Two programs to compare.

/- Template shape: start by proving the action profile. -/
example (hActs : ActionClaim left right Action.C Action.D) :
    ActionClaim left right Action.C Action.D := by
  simpa using hActs

/- From `ActionClaim`, extract each action directly without payoffs. -/
example (hActs : ActionClaim left right Action.C Action.D) :
  (playActions left right).1 = Action.C := by
  unfold ActionClaim at hActs
  simpa [playActions] using congrArg Prod.fst hActs

/- Symmetric right-side action extraction. -/
example (hActs : ActionClaim left right Action.C Action.D) :
    (playActions left right).2 = Action.D := by
  unfold ActionClaim at hActs
  simpa [playActions] using congrArg Prod.snd hActs

/- Optional Stage B: prove the full outcome record when you need payoffs. -/
example (hActs : ActionClaim left right Action.C Action.D)
    (hPayoffs : payoff m Action.C Action.D = 0 ∧ payoff m Action.D Action.C = 3) :
    OutcomeClaim m left right {
      leftAction := Action.C
      rightAction := Action.D
      leftPayoff := 0
      rightPayoff := 3
    } := by
  rcases hPayoffs with ⟨hL, hR⟩
  unfold OutcomeClaim
  unfold ActionClaim at hActs
  simp [playOutcome, mkOutcome, hActs, hL, hR]

end GenericTemplate

end PD.Proofs

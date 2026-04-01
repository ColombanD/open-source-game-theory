import PrisonersDilemma.Pipeline -- Import generic game pipeline definitions and claim predicates.

/-!
# Proof Workflow Template

Use this file as a pattern when adding a new paper/program family.

1. Define a program type in `PrisonersDilemma/Models/<Family>.lean`.
2. Provide `ProgramModel` semantics (`action : Prog → Prog → Action`).
3. Create theorem files in `PrisonersDilemma/Proofs/` that prove
   `ActionClaim` first, then `OutcomeClaim`.

The two-stage pattern keeps theorem-prover reasoning clean:
- Stage A: prove what each side does.
- Stage B: derive payoffs from the payoff matrix.
-/

namespace PD.Proofs -- Namespace for reusable proof patterns and concrete theorem files.

open PD -- Bring PD names (`ActionClaim`, `OutcomeClaim`, `playOutcome`, ...) into local scope.

section GenericTemplate -- Parameterized section reusable for any program type with a `ProgramModel`.

variable {Prog : Type} [ProgramModel Prog] -- Abstract program language plus its operational semantics.
variable (m : PayoffMatrix) -- Abstract payoff matrix used for outcome evaluation.
variable (left right : Prog) -- Two arbitrary programs to compare.

/-- Template shape: first prove the action profile. -/
example (hActs : ActionClaim left right Action.C Action.D) :
    (playOutcome m left right).leftAction = Action.C := by
  unfold ActionClaim at hActs -- Turn the claim hypothesis into an explicit equality on `playActions`.
  simp [playOutcome, mkOutcome, hActs] -- Expand outcome construction and rewrite via known actions.

/-- Template shape: then prove the full outcome record. -/
example (hActs : ActionClaim left right Action.C Action.D)
    (hPayoffs : payoff m Action.C Action.D = 0 ∧ payoff m Action.D Action.C = 3) :
    OutcomeClaim m left right {
      leftAction := Action.C
      rightAction := Action.D
      leftPayoff := 0
      rightPayoff := 3
    } := by
  rcases hPayoffs with ⟨hL, hR⟩ -- Split payoff assumptions into left and right equalities.
  unfold OutcomeClaim -- Expand target proposition to an equality of concrete outcomes.
  unfold ActionClaim at hActs -- Expand action-profile hypothesis for rewriting.
  simp [playOutcome, mkOutcome, hActs, hL, hR] -- Reduce the record fields using action and payoff equalities.

end GenericTemplate -- End generic proof template section.

end PD.Proofs -- End proofs namespace.

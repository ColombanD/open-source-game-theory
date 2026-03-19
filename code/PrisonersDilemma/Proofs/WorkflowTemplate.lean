import PrisonersDilemma.Pipeline

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

namespace PD.Proofs

open PD

section GenericTemplate

variable {Prog : Type} [ProgramModel Prog]
variable (m : PayoffMatrix)
variable (left right : Prog)

/-- Template shape: first prove the action profile. -/
example (hActs : ActionClaim left right Action.C Action.D) :
    (playOutcome m left right).leftAction = Action.C := by
  simp [ActionClaim, playOutcome, playActions] at hActs
  simpa [hActs]

/-- Template shape: then prove the full outcome record. -/
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
  simp [playOutcome, ActionClaim, mkOutcome, hActs, hL, hR]

end GenericTemplate

end PD.Proofs

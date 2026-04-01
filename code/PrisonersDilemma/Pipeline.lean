import PrisonersDilemma.Core -- Import definitions from `Core` (Action, PayoffMatrix, Outcome, mkOutcome, ...).

namespace PD -- Put all declarations in the `PD` namespace.

/-- A program model provides how a program acts when given opponent source/program. -/
class ProgramModel (Prog : Type) where -- Typeclass saying how programs of type `Prog` choose actions.
  action : Prog → Prog → Action -- Given me and my opponent, return my chosen PD action.

def playActions {Prog : Type} [ProgramModel Prog] (left right : Prog) : Action × Action := -- Compute both players' actions for a matchup.
  (ProgramModel.action left right, ProgramModel.action right left) -- Left acts against right; right acts against left.

def playOutcome {Prog : Type} [ProgramModel Prog] -- Compute the full outcome (actions + payoffs) for two programs.
    (m : PayoffMatrix) (left right : Prog) : Outcome :=
  let acts := playActions left right -- First compute the pair of actions.
  mkOutcome m acts.1 acts.2 -- Then convert those actions into an `Outcome` using matrix `m`.

/-- A proposition-level claim that a specific action pair occurs for a matchup. -/
def ActionClaim {Prog : Type} [ProgramModel Prog] -- Logical statement about which actions occur.
    (left right : Prog) (leftAction rightAction : Action) : Prop :=
  playActions left right = (leftAction, rightAction) -- Claim is true exactly when computed actions equal this pair.

/-- A proposition-level claim that a specific outcome record occurs. -/
def OutcomeClaim {Prog : Type} [ProgramModel Prog] -- Logical statement about which full outcome occurs.
    (m : PayoffMatrix) (left right : Prog) (o : Outcome) : Prop :=
  playOutcome m left right = o -- Claim is true exactly when the computed outcome equals `o`.

@[simp] theorem playActions_left {Prog : Type} [ProgramModel Prog] (left right : Prog) :
    (playActions left right).1 = ProgramModel.action left right := rfl -- First component of pair is left player's action.

@[simp] theorem playActions_right {Prog : Type} [ProgramModel Prog] (left right : Prog) :
    (playActions left right).2 = ProgramModel.action right left := rfl -- Second component is right player's action.

end PD -- Close the `PD` namespace.

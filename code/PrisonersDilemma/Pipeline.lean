import PrisonersDilemma.Core

namespace PD

/-- A program model provides how a program acts when given opponent source/program. -/
class ProgramModel (Prog : Type) where
  action : Prog → Prog → Action

def playActions {Prog : Type} [ProgramModel Prog] (left right : Prog) : Action × Action :=
  (ProgramModel.action left right, ProgramModel.action right left)

def playOutcome {Prog : Type} [ProgramModel Prog]
    (m : PayoffMatrix) (left right : Prog) : Outcome :=
  let acts := playActions left right
  mkOutcome m acts.1 acts.2

/-- A proposition-level claim that a specific action pair occurs for a matchup. -/
def ActionClaim {Prog : Type} [ProgramModel Prog]
    (left right : Prog) (leftAction rightAction : Action) : Prop :=
  playActions left right = (leftAction, rightAction)

/-- A proposition-level claim that a specific outcome record occurs. -/
def OutcomeClaim {Prog : Type} [ProgramModel Prog]
    (m : PayoffMatrix) (left right : Prog) (o : Outcome) : Prop :=
  playOutcome m left right = o

@[simp] theorem playActions_left {Prog : Type} [ProgramModel Prog] (left right : Prog) :
    (playActions left right).1 = ProgramModel.action left right := rfl

@[simp] theorem playActions_right {Prog : Type} [ProgramModel Prog] (left right : Prog) :
    (playActions left right).2 = ProgramModel.action right left := rfl

end PD

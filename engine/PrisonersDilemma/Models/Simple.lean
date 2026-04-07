import PrisonersDilemma.Pipeline -- Import the game pipeline abstractions and core PD definitions.

namespace PD.Models.Simple -- Namespace for the simplest concrete program model.

open PD -- Bring names like `Action`, `ProgramModel`, `playActions`, etc. into local scope.

inductive Program : Type where -- Two trivial programs: always cooperate or always defect.
  | cooperate -- Constructor representing the always-cooperate strategy.
  | defect -- Constructor representing the always-defect strategy.
  deriving DecidableEq, Repr -- Auto-generate equality checking and printable representation.

instance : ProgramModel Program where -- Provide how `Program` chooses an action against an opponent.
  SourceType := Unit
  source := fun _ => ()
  actionFromSource -- Define the required source-level semantics from the `ProgramModel` typeclass.
    | Program.cooperate, _ => Action.C -- Cooperator ignores opponent source and plays `C`.
    | Program.defect, _ => Action.D -- Defector ignores opponent source and plays `D`.

end PD.Models.Simple -- Close this model namespace.

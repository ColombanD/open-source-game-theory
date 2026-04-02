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

@[simp] theorem source_eq_unit (p : Program) : ProgramModel.source p = () := rfl

@[simp] theorem actionFromSource_eq
    (p : Program) (src : Unit) : ProgramModel.actionFromSource p src =
    (match p with
    | Program.cooperate => Action.C
    | Program.defect => Action.D) := by
  cases p <;> rfl

@[simp] theorem cooperate_vs_any (opp : Program) :
    ProgramModel.action Program.cooperate opp = Action.C := by -- Cooperator always returns `C`.
  cases opp <;> simp [ProgramModel.action]

@[simp] theorem defect_vs_any (opp : Program) :
    ProgramModel.action Program.defect opp = Action.D := by -- Defector always returns `D`.
  cases opp <;> simp [ProgramModel.action]

theorem cc_actions : -- Prove that cooperator vs cooperator yields `(C, C)` without using simp.
    playActions Program.cooperate Program.cooperate = (Action.C, Action.C) := by -- Cooperator vs cooperator yields `(C, C)`.
  unfold playActions -- Expand `playActions` into the pair of two `ProgramModel.action` calls.
  rw [cooperate_vs_any Program.cooperate] -- Rewrite left component to `Action.C`.

theorem cd_actions :
    playActions Program.cooperate Program.defect = (Action.C, Action.D) := by -- Cooperator vs defector yields `(C, D)`.
  simp [playActions] -- Unfold and simplify to the expected action pair.

theorem dd_actions :
    playActions Program.defect Program.defect = (Action.D, Action.D) := by -- Defector vs defector yields `(D, D)`.
  simp [playActions] -- Unfold and simplify to the expected action pair.

theorem cd_outcome_canonical :
    playOutcome canonicalPayoff Program.cooperate Program.defect = {
      leftAction := Action.C -- Left program is cooperator, so left action is `C`.
      rightAction := Action.D -- Right program is defector, so right action is `D`.
      leftPayoff := 0 -- In canonical PD, cooperator against defector gets 0.
      rightPayoff := 5 -- In canonical PD, defector against cooperator gets 5.
    } := by -- Prove the concrete canonical outcome for this matchup.
  simp [playOutcome, playActions, mkOutcome, payoff, canonicalPayoff] -- Expand definitions and let simplifier close the goal.

end PD.Models.Simple -- Close this model namespace.

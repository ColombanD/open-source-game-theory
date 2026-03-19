import PrisonersDilemma.Pipeline

namespace PD.Models.Simple

open PD

inductive Program : Type where
  | cooperate
  | defect
  deriving DecidableEq, Repr

instance : ProgramModel Program where
  action
    | Program.cooperate, _ => Action.C
    | Program.defect, _ => Action.D

@[simp] theorem cooperate_vs_any (opp : Program) :
    ProgramModel.action Program.cooperate opp = Action.C := by
  cases opp <;> rfl

@[simp] theorem defect_vs_any (opp : Program) :
    ProgramModel.action Program.defect opp = Action.D := by
  cases opp <;> rfl

theorem cc_actions :
    playActions Program.cooperate Program.cooperate = (Action.C, Action.C) := by
  simp [playActions]

theorem cd_actions :
    playActions Program.cooperate Program.defect = (Action.C, Action.D) := by
  simp [playActions]

theorem dd_actions :
    playActions Program.defect Program.defect = (Action.D, Action.D) := by
  simp [playActions]

theorem cd_outcome_canonical :
    playOutcome canonicalPayoff Program.cooperate Program.defect = {
      leftAction := Action.C
      rightAction := Action.D
      leftPayoff := 0
      rightPayoff := 5
    } := by
  simp [playOutcome, playActions, mkOutcome, payoff, canonicalPayoff]

end PD.Models.Simple

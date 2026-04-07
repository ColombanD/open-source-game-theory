import PrisonersDilemma.Models.Simple

namespace PD.Proofs.Simple

open PD
open PD.Action
open PD.Models.Simple

@[simp] theorem source_eq_unit (p : Program) : ProgramModel.source p = () := rfl

@[simp] theorem actionFromSource_eq
    (p : Program) (src : Unit) : ProgramModel.actionFromSource p src =
    (match p with
    | Program.cooperate => Action.C
    | Program.defect => Action.D) := by
  cases p <;> rfl

@[simp] theorem cooperate_vs_any (opp : Program) :
    ProgramModel.action Program.cooperate opp = Action.C := by
  cases opp <;> simp [ProgramModel.action]

@[simp] theorem defect_vs_any (opp : Program) :
    ProgramModel.action Program.defect opp = Action.D := by
  cases opp <;> simp [ProgramModel.action]

theorem cc_actions :
    playActions Program.cooperate Program.cooperate = (Action.C, Action.C) := by
  unfold playActions
  rw [cooperate_vs_any Program.cooperate]

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

end PD.Proofs.Simple

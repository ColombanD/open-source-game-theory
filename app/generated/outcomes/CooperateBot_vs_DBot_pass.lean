import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_DBot (n : Nat) :
    outcome (n+4) CooperateBot DBot = some (.C, .D) := by
  have hA : play (n+4) CooperateBot DBot = some .C := rfl
  have hB : play (n+4) DBot CooperateBot = some .D := by
    show eval (n+4) DBot CooperateBot DBot = some .D
    simp [eval, DBot, Prog.subst, CooperateBot, DefectBot]
    decide
  simp [outcome, hA, hB]

end PD.Theorems

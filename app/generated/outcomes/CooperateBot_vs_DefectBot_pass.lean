import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_DefectBot (n : Nat) :
    outcome (n+1) CooperateBot DefectBot = some (.C, .D) := by
  rfl

end PD.Theorems

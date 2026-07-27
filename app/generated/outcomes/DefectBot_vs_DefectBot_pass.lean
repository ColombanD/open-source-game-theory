import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DefectBot_vs_DefectBot (n : Nat) :
    outcome (n+1) DefectBot DefectBot = some (.D, .D) := by
  unfold outcome play eval DefectBot
  rfl

end PD.Theorems

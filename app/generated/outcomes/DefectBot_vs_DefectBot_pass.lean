import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_DefectBot_vs_DefectBot (n : Nat) :
    outcome (n+1) DefectBot DefectBot = some (.D, .D) := by
  rfl

end PDNew.Theorems

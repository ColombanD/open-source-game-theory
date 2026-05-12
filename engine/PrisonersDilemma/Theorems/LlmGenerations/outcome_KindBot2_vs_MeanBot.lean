import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.MeanBot

open PDNew
open PDNew.Bots

namespace PDNew.Bots
/-- KindBot2 always cooperates with any opponent. -/
def KindBot2 : Prog := .const Action.C
end PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_KindBot2_vs_MeanBot (n : Nat) :
    outcome (n+1) KindBot2 MeanBot = some (.C, .D) := by
  unfold outcome play eval KindBot2 MeanBot
  simp

end PDNew.Theorems

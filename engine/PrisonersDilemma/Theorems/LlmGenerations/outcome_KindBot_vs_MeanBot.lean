import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.KindBot
import PrisonersDilemma.Bots.LlmGenerations.MeanBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_KindBot_vs_MeanBot (n : Nat) :
    outcome (n+1) KindBot MeanBot = some (.C, .D) := by
  unfold outcome play eval KindBot MeanBot
  simp

end PDNew.Theorems

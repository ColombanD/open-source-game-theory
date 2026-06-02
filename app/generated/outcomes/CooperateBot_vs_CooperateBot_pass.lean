import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_CooperateBot_vs_CooperateBot (n : Nat) :
    outcome (n+1) CooperateBot CooperateBot = some (.C, .C) := by
  rfl

end PDNew.Theorems

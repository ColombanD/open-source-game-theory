import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_CooperateBot (n : Nat) :
    outcome (n+1) CooperateBot CooperateBot = some (.C, .C) := by
  simp [outcome, play, eval, CooperateBot]

end PD.Theorems


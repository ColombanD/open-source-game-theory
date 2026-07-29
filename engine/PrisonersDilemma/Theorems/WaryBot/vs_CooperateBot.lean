import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot vs CooperateBot: mutual cooperation at EVERY budget — the guard
    "¬(CooperateBot plays C)" is semantically false, so soundness refutes it
    outright (no floor needed). -/
theorem outcome_WaryBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 2) (WaryBot k) CooperateBot = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_vs_CooperateBot k fuel)
    (play_CooperateBot (fuel + 1) _)
end PD.Theorems

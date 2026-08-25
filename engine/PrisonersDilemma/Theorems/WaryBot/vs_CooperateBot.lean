import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot vs CooperateBot: mutual cooperation at EVERY budget — the guard
    "¬(CooperateBot plays C)" is semantically false, so soundness refutes it
    outright (no floor needed). -/
@[outcome]
theorem outcome_WaryBot_vs_CooperateBot :
    OutcomeSpec .universal 2
      WaryBot (fun _ => CooperateBot) (some (.C, .C)) :=
  fun k fuel =>
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_vs_CooperateBot k fuel)
    (play_CooperateBot (fuel + 1) _)
end PD.Theorems

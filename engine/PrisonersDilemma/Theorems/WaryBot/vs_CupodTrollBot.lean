import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs CupodTrollBot 2: mutual cooperation — WaryBot's guard hits the
    size floor; the troll's identity guard fails (WaryBot is not CupodBot). -/
theorem outcome_WaryBot_vs_CupodTrollBot (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (CupodTrollBot 2) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (CupodTrollBot_cooperates_if_opp_not_CupodBot 2 fuel (WaryBot 2) (by decide))
end PD.Theorems

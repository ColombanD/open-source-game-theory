import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs CupodTrollBot 2: `(D, C)` — the troll's identity guard
    fails (LegibleBot is not CupodBot) so it cooperates, and is exploited by the
    floor-defector. -/
theorem outcome_LegibleBot_vs_CupodTrollBot (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CupodTrollBot 2) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (CupodTrollBot_cooperates_if_opp_not_CupodBot 2 fuel (LegibleBot 2 2) (by decide))
end PD.Theorems

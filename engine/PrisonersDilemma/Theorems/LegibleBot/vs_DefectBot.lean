import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs DefectBot: mutual defection (floor). -/
theorem outcome_LegibleBot_vs_DefectBot (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (play_DefectBot (fuel + 1) _)
end PD.Theorems

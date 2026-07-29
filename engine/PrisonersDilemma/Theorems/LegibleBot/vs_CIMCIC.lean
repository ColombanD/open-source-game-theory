import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs CIMCIC 2: mutual defection — both guards hit the size
    floor and both else-branches defect. -/
theorem outcome_LegibleBot_vs_CIMCIC (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CIMCIC 2) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (CIMCIC2_plays_D_against_LegibleBot22 fuel)
end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs DIMCID 2: mutual cooperation — both guards hit the size floor
    and both bots' else-branches trust. -/
theorem outcome_WaryBot_vs_DIMCID (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (DIMCID 2) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (DIMCID2_plays_C_against_WaryBot2 fuel)
end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs DIMCID 2: `(D, C)` — the floor-defector exploits the
    floor-trusting DIMCID. -/
theorem outcome_LegibleBot_vs_DIMCID (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (DIMCID 2) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (DIMCID2_plays_C_against_LegibleBot22 fuel)
end PD.Theorems

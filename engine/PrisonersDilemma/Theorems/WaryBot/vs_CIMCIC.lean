import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs CIMCIC 2: `(C, D)` — BOTH guards hit the size floor; WaryBot's
    floor trusts, CIMCIC's floor defects. -/
theorem outcome_WaryBot_vs_CIMCIC (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (CIMCIC 2) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (CIMCIC2_plays_D_against_WaryBot2 fuel)
end PD.Theorems

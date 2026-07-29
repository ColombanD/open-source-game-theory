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

/-- LegibleBot vs CIMCIC, the whole FLOOR regime (same budget both sides):
    both guards outgrow the budget and both else-branches defect — mutual
    defection. Large-`k` needs a `.box` prover AND an `.impl` prover. -/
theorem outcome_LegibleBot_vs_CIMCIC_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (CIMCIC k) .C)).size) :
    outcome (fuel + 2) (LegibleBot k k) (CIMCIC k) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (CIMCIC_plays_D_against_LegibleBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_CIMCIC_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CIMCIC 2) = some (.D, .D) :=
  outcome_LegibleBot_vs_CIMCIC_floor 2 fuel (by decide) (by decide)
end PD.Theorems

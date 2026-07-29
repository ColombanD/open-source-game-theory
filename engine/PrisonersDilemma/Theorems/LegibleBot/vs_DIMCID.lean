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

/-- LegibleBot vs DIMCID, the whole FLOOR regime: the floor-defector exploits
    the floor-trusting DIMCID — `(D, C)`. Large-`k` needs a `.box` prover AND
    an `.impl` prover. -/
theorem outcome_LegibleBot_vs_DIMCID_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (DIMCID k) .C)).size)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (DIMCID k) .D)).size) :
    outcome (fuel + 2) (LegibleBot k k) (DIMCID k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (DIMCID_plays_C_against_LegibleBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_DIMCID_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (DIMCID 2) = some (.D, .C) :=
  outcome_LegibleBot_vs_DIMCID_floor 2 fuel (by decide) (by decide)
end PD.Theorems

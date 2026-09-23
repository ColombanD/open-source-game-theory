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

/-- WaryBot vs DIMCID, the whole FLOOR regime: both guards outgrow the budget
    and both else-branches trust — mutual cooperation. Large-`k` is OPEN
    (needs an `.impl` prover for DIMCID's guard). -/
theorem outcome_WaryBot_vs_DIMCID_floor (k fuel : Nat)
    (hszW : k < (Formula.neg (.plays (DIMCID k) (WaryBot k) .C)).size)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (WaryBot k) .C)
      (.plays (WaryBot k) (DIMCID k) .D)).size) :
    outcome (fuel + 2) (WaryBot k) (DIMCID k) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor k fuel _ hszW)
    (DIMCID_plays_C_against_WaryBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_DIMCID_floor2 (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (DIMCID 2) = some (.C, .C) :=
  outcome_WaryBot_vs_DIMCID_floor 2 fuel (by decide) (by decide)
end PD.Theorems

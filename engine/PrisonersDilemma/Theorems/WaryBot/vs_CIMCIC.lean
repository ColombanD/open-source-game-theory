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

/-- WaryBot vs CIMCIC, the whole FLOOR regime (same budget `k` on both sides):
    both guards outgrow the budget; WaryBot's floor trusts, CIMCIC's floor
    defects — `(C, D)`. Large-`k` is OPEN (needs an `.impl` prover for CIMCIC's
    guard). -/
theorem outcome_WaryBot_vs_CIMCIC_floor (k fuel : Nat)
    (hszW : k < (Formula.neg (.plays (CIMCIC k) (WaryBot k) .C)).size)
    (hszI : k < (Formula.impl (.plays (CIMCIC k) (WaryBot k) .C)
      (.plays (WaryBot k) (CIMCIC k) .C)).size) :
    outcome (fuel + 2) (WaryBot k) (CIMCIC k) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor k fuel _ hszW)
    (CIMCIC_plays_D_against_WaryBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_CIMCIC_floor2 (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (CIMCIC 2) = some (.C, .D) :=
  outcome_WaryBot_vs_CIMCIC_floor 2 fuel (by decide) (by decide)
end PD.Theorems

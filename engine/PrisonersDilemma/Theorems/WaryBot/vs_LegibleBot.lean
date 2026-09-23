import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Theorems.LegibleBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot vs LegibleBot, the whole FLOOR regime (both single-dial at `k`):
    WaryBot's floor trusts, LegibleBot's floor (illegible to itself) defects —
    `(C, D)`. Large-`k` is OPEN on BOTH sides (`.box` prover for LegibleBot,
    then WaryBot's response). -/
theorem outcome_WaryBot_vs_LegibleBot_floor (k fuel : Nat)
    (hszW : k < (Formula.neg (.plays (LegibleBot k k) (WaryBot k) .C)).size)
    (hszL : k < (Formula.box k (.plays (LegibleBot k k) (WaryBot k) .C)).size) :
    outcome (fuel + 2) (WaryBot k) (LegibleBot k k) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor k fuel _ hszW)
    (LegibleBot_defects_floor k k fuel (WaryBot k) hszL)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_LegibleBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (LegibleBot 2 2) = some (.C, .D) :=
  outcome_WaryBot_vs_LegibleBot_floor 2 fuel (by decide) (by decide)
end PD.Theorems

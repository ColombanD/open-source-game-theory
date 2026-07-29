import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs CupodTrollBot, the whole FLOOR regime: the troll's identity
    guard fails at EVERY budget (a `.box`-guard searcher is not CupodBot), so
    it cooperates and is exploited by the floor-defector — `(D, C)`.
    The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_CupodTrollBot_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (CupodTrollBot k) .C)).size) :
    outcome (fuel + 2) (LegibleBot k k) (CupodTrollBot k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (LegibleBot k k)
      (by simp [LegibleBot, CupodBot]))

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_CupodTrollBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CupodTrollBot 2) = some (.D, .C) :=
  outcome_LegibleBot_vs_CupodTrollBot_floor 2 fuel (by decide)
end PD.Theorems

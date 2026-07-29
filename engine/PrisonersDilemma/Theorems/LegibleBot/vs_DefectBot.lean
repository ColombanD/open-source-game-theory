import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs DefectBot, the whole FLOOR regime: mutual defection.
    The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_DefectBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) DefectBot .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (play_DefectBot (fuel + 1) _)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_DefectBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) DefectBot = some (.D, .D) :=
  outcome_LegibleBot_vs_DefectBot_floor 2 2 fuel (by decide)
end PD.Theorems

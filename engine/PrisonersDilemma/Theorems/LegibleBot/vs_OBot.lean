import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs OBot, the whole FLOOR regime: OBot's CooperateBot probe sees
    the floor-defection — mutual defection. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_OBot_floor (kOut kIn fuel : Nat)
    (hszO : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) OBot .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) OBot = some (.D, .D) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) OBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) OBot hszO
  exact outcome_of_plays _ _ _ _ _ hA
    (OBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszCB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_OBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) OBot = some (.D, .D) :=
  outcome_LegibleBot_vs_OBot_floor 2 2 fuel (by decide) (by decide)
end PD.Theorems

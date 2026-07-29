import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs TitForTatBot, the whole FLOOR regime: TFT's probe sees the
    floor-defection and punishes — mutual defection. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_TitForTatBot_floor (kOut kIn fuel : Nat)
    (hszT : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) TitForTatBot .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) TitForTatBot = some (.D, .D) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) TitForTatBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) TitForTatBot hszT
  exact outcome_of_plays _ _ _ _ _ hA
    (TitForTatBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszCB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_TitForTatBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) TitForTatBot = some (.D, .D) :=
  outcome_LegibleBot_vs_TitForTatBot_floor 2 2 fuel (by decide) (by decide)
end PD.Theorems

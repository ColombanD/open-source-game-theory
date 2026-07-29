import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs EBot, the whole FLOOR regime: all three of EBot's probes see
    the floor-defection — mutual defection. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_EBot_floor (kOut kIn fuel : Nat)
    (hszE : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) EBot .C)).size)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot MirrorBot) .C)).size) :
    outcome (fuel + 6) (LegibleBot kOut kIn) EBot = some (.D, .D) := by
  have hA : play (fuel + 6) (LegibleBot kOut kIn) EBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 4) EBot hszE
  exact outcome_of_plays _ _ _ _ _ hA
    (EBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszDB hszCB hszM)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_EBot_floor2 (fuel : Nat) :
    outcome (fuel + 6) (LegibleBot 2 2) EBot = some (.D, .D) :=
  outcome_LegibleBot_vs_EBot_floor 2 2 fuel
    (by decide) (by decide) (by decide) (by decide)
end PD.Theorems

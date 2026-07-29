import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs DBot, the whole FLOOR regime: DBot only exploits bots that
    cooperate with defectors; the floor-defector is spared and DBot cooperates —
    `(D, C)`. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_DBot_floor (kOut kIn fuel : Nat)
    (hszD : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) DBot .C)).size)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) DBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) DBot hszD
  exact outcome_of_plays _ _ _ _ _ hA
    (DBot_plays_C_against_LegibleBot_floor kOut kIn fuel hszDB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_DBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) DBot = some (.D, .C) :=
  outcome_LegibleBot_vs_DBot_floor 2 2 fuel (by decide) (by decide)
end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs MirrorBot, the whole FLOOR regime: the mirror replays the
    floor-defection — mutual defection. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_MirrorBot_floor (kOut kIn fuel : Nat)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) MirrorBot .C)).size) :
    outcome (fuel + 3) (LegibleBot kOut kIn) MirrorBot = some (.D, .D) := by
  have hA : play (fuel + 3) (LegibleBot kOut kIn) MirrorBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 1) MirrorBot hszM
  exact outcome_of_plays _ _ _ _ _ hA
    (MirrorBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszM)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_MirrorBot_floor2 (fuel : Nat) :
    outcome (fuel + 3) (LegibleBot 2 2) MirrorBot = some (.D, .D) :=
  outcome_LegibleBot_vs_MirrorBot_floor 2 2 fuel (by decide)
end PD.Theorems

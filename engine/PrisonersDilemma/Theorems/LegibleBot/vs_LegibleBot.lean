import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot self-play, the whole FLOOR regime: neither copy can see its own
    legibility, so neither cooperates — the tragic dual of WaryBot's
    floor-trust. Large-`k` self-play is the full two-box Löb fixpoint, OPEN. -/
theorem outcome_LegibleBot_vs_LegibleBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (LegibleBot kOut kIn) .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) (LegibleBot kOut kIn) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (LegibleBot_defects_floor kOut kIn fuel _ hsz)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_LegibleBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (LegibleBot 2 2) = some (.D, .D) :=
  outcome_LegibleBot_vs_LegibleBot_floor 2 2 fuel (by decide)
end PD.Theorems

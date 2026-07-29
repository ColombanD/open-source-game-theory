import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs CooperateBot, the whole FLOOR regime: the floor-blind
    moralist of transparency EXPLOITS the unconditional cooperator — below the
    size floor it cannot certify its own legibility, so it defects on
    principle. The non-floor regime (guard fits, needs a `.box` prover) is OPEN. -/
theorem outcome_LegibleBot_vs_CooperateBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) CooperateBot .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) CooperateBot = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (play_CooperateBot (fuel + 1) _)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_CooperateBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) CooperateBot = some (.D, .C) :=
  outcome_LegibleBot_vs_CooperateBot_floor 2 2 fuel (by decide)
end PD.Theorems

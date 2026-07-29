import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot self-play, the whole FLOOR regime: neither copy can afford to
    refute the other's cooperation, so both trust — the refutation-side mirror
    of Löbian self-cooperation. Large-`k` self-play is OPEN (the `.neg`-guard
    fixpoint). -/
theorem outcome_WaryBot_vs_WaryBot_floor (k fuel : Nat)
    (hsz : k < (Formula.neg (.plays (WaryBot k) (WaryBot k) .C)).size) :
    outcome (fuel + 2) (WaryBot k) (WaryBot k) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor k fuel _ hsz)
    (WaryBot_cooperates_floor k fuel _ hsz)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_WaryBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (WaryBot 2) = some (.C, .C) :=
  outcome_WaryBot_vs_WaryBot_floor 2 fuel (by decide)
end PD.Theorems

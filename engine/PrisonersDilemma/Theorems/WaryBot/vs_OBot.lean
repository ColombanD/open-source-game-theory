import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot vs OBot, the whole FLOOR regime: the CooperateBot probe clears at
    every budget (soundness); the DefectBot probe and WaryBot's own guard need
    the floor — mutual cooperation. The large-`k` outcome is OPEN and expected
    to FLIP to `(C, D)`: a defended WaryBot fails OBot's second probe, and
    refuting OBot's cooperation then needs `¬Pf` of a TRUE formula whose
    certificate crosses WaryBot's own failed search (a `.neg`-spine floor
    census, not yet formalized). -/
theorem outcome_WaryBot_vs_OBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size)
    (hszO : k < (Formula.neg (.plays OBot (WaryBot k) .C)).size) :
    outcome (fuel + 5) (WaryBot k) OBot = some (.C, .C) := by
  have hA : play (fuel + 5) (WaryBot k) OBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_floor k (fuel + 3) OBot hszO
  exact outcome_of_plays _ _ _ _ _ hA
    (OBot_plays_C_against_WaryBot_floor k fuel hszDB)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_OBot_floor2 (fuel : Nat) :
    outcome (fuel + 5) (WaryBot 2) OBot = some (.C, .C) :=
  outcome_WaryBot_vs_OBot_floor 2 fuel (by decide) (by decide)
end PD.Theorems

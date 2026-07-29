import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **The budget phase transition, floor side**: at `k = 2` WaryBot cannot afford
    the refutation of even a pure defector's cooperation (guard size 12 > 2), so
    it trusts and is EXPLOITED. -/
theorem outcome_WaryBot_vs_DefectBot_floor (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) DefectBot = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (play_DefectBot (fuel + 1) _)

/-- **The budget phase transition, defended side**: at `k = 16` the `Pf.atomNeg`
    transcript exactly fits and WaryBot defends itself. Together with `_floor`
    this is the machine-checked threshold pair from the deterministic pre-pass. -/
theorem outcome_WaryBot_vs_DefectBot_defended (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 16) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot16_defects_vs_DefectBot fuel)
    (play_DefectBot (fuel + 1) _)
end PD.Theorems

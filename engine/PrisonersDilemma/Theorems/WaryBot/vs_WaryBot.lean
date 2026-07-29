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

/-- WaryBot 2 self-play: mutual cooperation BY THE SIZE FLOOR — neither copy can
    afford to refute the other's cooperation, so both trust. The refutation-side
    mirror of Löbian self-cooperation. -/
theorem outcome_WaryBot_vs_WaryBot (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (WaryBot 2) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (WaryBot_cooperates_floor 2 fuel _ (by decide))
end PD.Theorems

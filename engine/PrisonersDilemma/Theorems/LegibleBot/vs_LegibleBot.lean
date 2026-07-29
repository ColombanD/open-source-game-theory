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

/-- LegibleBot 2 2 self-play: mutual defection by the size floor — neither copy
    can see its own legibility, so neither cooperates. The tragic dual of
    WaryBot's floor-trust. -/
theorem outcome_LegibleBot_vs_LegibleBot (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (LegibleBot 2 2) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (LegibleBot_defects_floor 2 2 fuel _ (by decide))
end PD.Theorems

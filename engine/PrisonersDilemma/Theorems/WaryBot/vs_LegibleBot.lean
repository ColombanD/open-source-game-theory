import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Theorems.LegibleBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs LegibleBot 2 2: `(C, D)` — both guards hit the size floor;
    WaryBot's floor trusts, LegibleBot's floor (illegible to itself) defects. -/
theorem outcome_WaryBot_vs_LegibleBot (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (LegibleBot 2 2) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (LegibleBot_defects_floor 2 2 fuel (WaryBot 2) (by decide))
end PD.Theorems

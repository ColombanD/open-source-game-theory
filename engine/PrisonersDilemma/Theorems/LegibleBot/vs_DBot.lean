import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs DBot: `(D, C)` — DBot only exploits bots that cooperate
    with defectors; the floor-defector is spared and DBot cooperates. -/
theorem outcome_LegibleBot_vs_DBot (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (LegibleBot 2 2) DBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor 2 2 (fuel + 2) DBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (DBot_plays_C_against_LegibleBot22 fuel)
end PD.Theorems

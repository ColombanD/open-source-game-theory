import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs EBot: mutual defection — all three of EBot's probes see
    the floor-defection. -/
theorem outcome_LegibleBot_vs_EBot (fuel : Nat) :
    outcome (fuel + 6) (LegibleBot 2 2) EBot = some (.D, .D) := by
  have hA : play (fuel + 6) (LegibleBot 2 2) EBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor 2 2 (fuel + 4) EBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (EBot_plays_D_against_LegibleBot22 fuel)
end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs TitForTatBot: mutual defection — TFT's probe sees the
    floor-defection and punishes. -/
theorem outcome_LegibleBot_vs_TitForTatBot (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) TitForTatBot = some (.D, .D) := by
  have hA : play (fuel + 4) (LegibleBot 2 2) TitForTatBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor 2 2 (fuel + 2) TitForTatBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (TitForTatBot_plays_D_against_LegibleBot22 fuel)
end PD.Theorems

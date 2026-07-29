import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs TitForTatBot: mutual cooperation — TFT's probe sees the
    floor-forced trust. -/
theorem outcome_WaryBot_vs_TitForTatBot (fuel : Nat) :
    outcome (fuel + 4) (WaryBot 2) TitForTatBot = some (.C, .C) := by
  have hA : play (fuel + 4) (WaryBot 2) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor 2 (fuel + 2) TitForTatBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (TitForTatBot_plays_C_against_WaryBot2 fuel)
end PD.Theorems

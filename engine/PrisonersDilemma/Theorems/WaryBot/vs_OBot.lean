import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs OBot: mutual cooperation — OBot's two probes both clear the
    floor-trusting WaryBot. -/
theorem outcome_WaryBot_vs_OBot (fuel : Nat) :
    outcome (fuel + 5) (WaryBot 2) OBot = some (.C, .C) := by
  have hA : play (fuel + 5) (WaryBot 2) OBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor 2 (fuel + 3) OBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (OBot_plays_C_against_WaryBot2 fuel)
end PD.Theorems

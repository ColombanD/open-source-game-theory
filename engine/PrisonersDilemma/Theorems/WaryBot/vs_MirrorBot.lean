import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs MirrorBot: mutual cooperation — the mirror replays the
    floor-forced trust. -/
theorem outcome_WaryBot_vs_MirrorBot (fuel : Nat) :
    outcome (fuel + 3) (WaryBot 2) MirrorBot = some (.C, .C) := by
  have hA : play (fuel + 3) (WaryBot 2) MirrorBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor 2 (fuel + 1) MirrorBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (MirrorBot_plays_C_against_WaryBot2 fuel)
end PD.Theorems

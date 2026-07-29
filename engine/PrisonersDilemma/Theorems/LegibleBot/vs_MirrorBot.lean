import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs MirrorBot: mutual defection — the mirror replays the
    floor-defection. -/
theorem outcome_LegibleBot_vs_MirrorBot (fuel : Nat) :
    outcome (fuel + 3) (LegibleBot 2 2) MirrorBot = some (.D, .D) := by
  have hA : play (fuel + 3) (LegibleBot 2 2) MirrorBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor 2 2 (fuel + 1) MirrorBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (MirrorBot_plays_D_against_LegibleBot22 fuel)
end PD.Theorems

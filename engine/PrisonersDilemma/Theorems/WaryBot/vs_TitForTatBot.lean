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

/-- WaryBot vs TitForTatBot: mutual cooperation at EVERY budget — TFT's probe
    clears WaryBot by soundness (refuting the probe's cooperation is
    semantically impossible), and TFT's cooperation is in turn irrefutable.
    No floor, no threshold: the clean soundness-only cell. -/
theorem outcome_WaryBot_vs_TitForTatBot (k fuel : Nat) :
    outcome (fuel + 4) (WaryBot k) TitForTatBot = some (.C, .C) := by
  have hA : play (fuel + 4) (WaryBot k) TitForTatBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_vs_TitForTatBot k (fuel + 2)
  exact outcome_of_plays _ _ _ _ _ hA (TitForTatBot_plays_C_against_WaryBot k fuel)

end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs OBot: mutual defection. -/
theorem outcome_DupocBot_vs_OBot (fuel : Nat) :
    ∃ k, outcome (fuel + 5) (DupocBot k) OBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_bot_CooperateBot
  refine ⟨k, ?_⟩
  have hA : play (fuel + 5) (DupocBot k) OBot = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_OBot k (fuel + 3) hk
  have hB : play (fuel + 5) OBot (DupocBot k) = some .D :=
    OBot_plays_D_against_DupocBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

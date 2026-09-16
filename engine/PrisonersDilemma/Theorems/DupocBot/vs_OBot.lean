import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs OBot: mutual defection. -/
@[outcome]
theorem outcome_DupocBot_vs_OBot :
    OutcomeSpec .eventual 5
      DupocBot (fun _ => OBot) (some (.D, .D)) := by
  -- The `.bot CooperateBot` certificate pays the atom's size (`Nat.log2 k + 12`, the
  -- recost of 2026-09-16), so the threshold comes from `linear_log2_add_le`.
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 12
  refine ⟨K, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_bot_CooperateBot_ge k (by have := hK k (Nat.le_of_lt hlt); omega)
  have hA : play (fuel + 5) (DupocBot k) OBot = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_OBot k (fuel + 3) hk
  have hB : play (fuel + 5) OBot (DupocBot k) = some .D :=
    OBot_plays_D_against_DupocBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

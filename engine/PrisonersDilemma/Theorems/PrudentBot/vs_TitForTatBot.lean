import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- TitForTatBot --

/-- TFT defects against PrudentBot: TFT probes PrudentBot against `.bot CooperateBot`,
    sees it defect (guard D ≠ test C), takes its else-branch and defects. -/
theorem TFT_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) TitForTatBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) TitForTatBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) TitForTatBot (PrudentBot k) TitForTatBot = some .D
  rw [show TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.const Action.C) (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_TFT_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) TitForTatBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using TFT_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) TitForTatBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_TFT_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays TitForTatBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_TFT_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_TFT (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) TitForTatBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel TitForTatBot
    (proofSearch_false_TFT_vs_PrudentBot k)

/-- PrudentBot vs TitForTatBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) TitForTatBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) TitForTatBot = some .D := by
    simpa using PrudentBot_plays_D_against_TFT k 4
  have hB : play 6 TitForTatBot (PrudentBot k) = some .D := by
    simpa using TFT_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems

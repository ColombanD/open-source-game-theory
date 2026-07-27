import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DupocBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_EBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_MirrorBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_OBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- OBot --

/-- OBot defects against PrudentBot: OBot's first probe is the opponent against
    `.bot CooperateBot`; PrudentBot defects there (D ≠ test C), so OBot takes its
    outermost else-branch and defects. -/
theorem OBot_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 5) OBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 4) OBot (PrudentBot k)
      (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) OBot (PrudentBot k) CooperateBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 4) OBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) OBot (PrudentBot k) OBot = some .D
  rw [show OBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem interp_OBot_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays OBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) OBot (PrudentBot k) = some .D := by
    simpa [Nat.add_assoc] using OBot_plays_D_vs_PrudentBot k (n + 1)
  have hC : play (n + 6) OBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD; cases hD

theorem proofSearch_false_OBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays OBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_OBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) OBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel OBot
    (proofSearch_false_OBot_vs_PrudentBot k)

/-- PrudentBot vs OBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) OBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) OBot = some .D := by
    simpa using PrudentBot_plays_D_against_OBot k 4
  have hB : play 6 OBot (PrudentBot k) = some .D := by
    simpa using OBot_plays_D_vs_PrudentBot k 1
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems

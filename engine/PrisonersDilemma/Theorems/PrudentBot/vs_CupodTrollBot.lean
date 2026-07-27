import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot
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

-- CupodTrollBot --

theorem CupodTrollBot_never_D_vs_botDefect (k : Nat) :
    ¬ ∃ n, play n (CupodTrollBot k) (.bot DefectBot) = some .D := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (CupodTrollBot k) (.bot DefectBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k n DefectBot
  have hn' : eval n (CupodTrollBot k) (.bot DefectBot) (CupodTrollBot k) = some .D := hn
  have hD : play (n + 2) (CupodTrollBot k) (.bot DefectBot) = some .D :=
    eval_mono_le hn' (n + 2) (by omega)
  rw [hC] at hD
  simp at hD

theorem PrudentBot_defects_vs_CupodTrollBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (CupodTrollBot k) = some .D := by
  have hφ2 : proofSearch k (.plays (CupodTrollBot k) (.bot DefectBot) .D) = false := by
    cases hps : proofSearch k (.plays (CupodTrollBot k) (.bot DefectBot) .D) with
    | true => exact absurd (proofSearch_sound _ _ hps) (CupodTrollBot_never_D_vs_botDefect k)
    | false => rfl
  show eval (fuel + 3) (PrudentBot k) (CupodTrollBot k) (PrudentBot k) = some .D
  unfold PrudentBot
  simp [eval, Prog.subst, Formula.subst, hφ2]

theorem outcome_PrudentBot_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) (CupodTrollBot k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨3, ?_⟩⟩
  have hA : play 3 (PrudentBot k) (CupodTrollBot k) = some .D :=
    PrudentBot_defects_vs_CupodTrollBot k 0
  have hB : play 3 (CupodTrollBot k) (PrudentBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k 1 (PrudentBot k)
      (by simp [PrudentBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems

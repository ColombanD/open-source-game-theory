import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- CupodTrollBot never plays D against `.bot CooperateBot` (it cooperates there). -/
theorem guardian_ctb_CupodTrollBot_never_D_vs_botCB (k : Nat) :
    ¬ (Formula.plays (CupodTrollBot k) (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (CupodTrollBot k) (.bot CooperateBot) = some .C :=
    CupodTrollBot_cooperates_against_bot k n CooperateBot
  have hn' : eval n (CupodTrollBot k) (.bot CooperateBot) (CupodTrollBot k) = some .D := hn
  have hD : play (n + 2) (CupodTrollBot k) (.bot CooperateBot) = some .D :=
    eval_mono_le hn' (n + 2) (by omega)
  rw [hC] at hD
  simp at hD

/-- GuardianBot's guard against CupodTrollBot is refuted at every budget. -/
theorem guardian_ctb_guard_false (k : Nat) :
    proofSearch k (.plays (CupodTrollBot k) (.bot CooperateBot) .D) = false := by
  cases hps : proofSearch k (.plays (CupodTrollBot k) (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ hps)
                          (guardian_ctb_CupodTrollBot_never_D_vs_botCB k)
  | false => rfl

/-- GuardianBot cooperates against CupodTrollBot (guard refuted). -/
theorem GuardianBot_cooperates_vs_CupodTrollBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (CupodTrollBot k) = some .C := by
  have hg := guardian_ctb_guard_false k
  show eval (fuel + 2) (GuardianBot k) (CupodTrollBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_GuardianBot_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (CupodTrollBot k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (CupodTrollBot k) = some .C :=
    GuardianBot_cooperates_vs_CupodTrollBot k 0
  have hB : play 2 (CupodTrollBot k) (GuardianBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k 0 (GuardianBot k)
      (by simp [GuardianBot, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem guardian_cupod_guard_false (k : Nat) :
    proofSearch k (.plays (CupodBot k) (.bot CooperateBot) .D) = false := by
  cases hps : proofSearch k (.plays (CupodBot k) (.bot CooperateBot) .D) with
  | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ hps
      have hC : play (n + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
        CupodBot_plays_C_against_bot_CooperateBot k n
      have hD : play (n + 2) (CupodBot k) (.bot CooperateBot) = some .D :=
        eval_mono_le hn (n + 2) (by omega)
      rw [hC] at hD; simp at hD
  | false => rfl

theorem GuardianBot_cooperates_vs_CupodBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (CupodBot k) = some .C := by
  have hg := guardian_cupod_guard_false k
  show eval (fuel + 2) (GuardianBot k) (CupodBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem interp_GuardianBot_plays_D_vs_CupodBot_false (k : Nat) :
    ¬ (Formula.plays (GuardianBot k) (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (GuardianBot k) (CupodBot k) = some .C :=
    GuardianBot_cooperates_vs_CupodBot k n
  have hD : play (n + 2) (GuardianBot k) (CupodBot k) = some .D :=
    eval_mono_le hn (n + 2) (by omega)
  rw [hC] at hD; simp at hD

theorem cupod_guardian_guard_false (k : Nat) :
    proofSearch k (.plays (GuardianBot k) (CupodBot k) .D) = false := by
  cases hps : proofSearch k (.plays (GuardianBot k) (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ hps)
                          (interp_GuardianBot_plays_D_vs_CupodBot_false k)
  | false => rfl

theorem CupodBot_cooperates_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (GuardianBot k) = some .C := by
  have hg := cupod_guardian_guard_false k
  show eval (fuel + 2) (CupodBot k) (GuardianBot k) (CupodBot k) = some .C
  show eval (fuel + 2) (CupodBot k) (GuardianBot k)
    (.search k (.plays .opp .self .D) (.const .D) (.const .C)) = some .C
  simp only [eval]
  show (if proofSearch k (.plays (GuardianBot k) (CupodBot k) .D) = true
        then eval (fuel + 1) (CupodBot k) (GuardianBot k) (.const .D)
        else eval (fuel + 1) (CupodBot k) (GuardianBot k) (.const .C)) = some .C
  rw [hg]
  simp [eval]

theorem llm_outcome_GuardianBot_vs_CupodBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (CupodBot k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (CupodBot k) = some .C :=
    GuardianBot_cooperates_vs_CupodBot k 0
  have hB : play 2 (CupodBot k) (GuardianBot k) = some .C :=
    CupodBot_cooperates_vs_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

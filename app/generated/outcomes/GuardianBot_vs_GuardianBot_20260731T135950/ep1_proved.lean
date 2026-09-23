import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD PD.Bots PD.BaseTheorems
namespace PD.Theorems

/-- GuardianBot does not bully the frozen CB probe: it plays C vs `.bot CooperateBot`. -/
theorem gg_guardian_C_vs_botCB (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (.bot CooperateBot) = some .C := by
  have hg : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) with
    | true  => exact absurd (proofSearch_sound _ _ h)
                            (interp_bot_CooperateBot_plays_D_false _)
    | false => rfl
  show eval (fuel + 2) (GuardianBot k) (.bot CooperateBot) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- The self-guard "GuardianBot plays D vs botCB" is false at every fuel. -/
theorem gg_interp_guardian_botCB_D_false (k : Nat) :
    ¬ (Formula.plays (GuardianBot k) (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 2) (GuardianBot k) (.bot CooperateBot) = some .C := gg_guardian_C_vs_botCB k n
  have hD : play (n + 2) (GuardianBot k) (.bot CooperateBot) = some .D := by
    unfold play at hn ⊢
    exact eval_mono_le hn (n+2) (by omega)
  rw [hC] at hD; cases hD

/-- The self-guard is refuted at every budget (unfolded search form). -/
theorem gg_proofSearch_false (k : Nat) :
    proofSearch k (.plays
      (Prog.search k (Formula.plays Prog.opp (.bot CooperateBot) Action.D)
        (.const Action.D) (.const Action.C)) (.bot CooperateBot) .D) = false := by
  have h := gg_interp_guardian_botCB_D_false k
  unfold GuardianBot at h
  cases hh : proofSearch k (.plays
      (Prog.search k (Formula.plays Prog.opp (.bot CooperateBot) Action.D)
        (.const Action.D) (.const Action.C)) (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ hh) h
  | false => rfl

/-- GuardianBot cooperates with GuardianBot: the self-guard is refuted, else-branch trusts. -/
theorem gg_guardian_C_vs_guardian (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (GuardianBot k) = some .C := by
  have hg := gg_proofSearch_false k
  show eval (fuel + 2) (GuardianBot k) (GuardianBot k) (GuardianBot k) = some .C
  conv_lhs => unfold GuardianBot
  simp only [eval, Prog.subst, Formula.subst]
  rw [hg]
  rfl

theorem llm_outcome_GuardianBot_vs_GuardianBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) (GuardianBot k) = some (.C, .C) := by
  refine ⟨0, fun k hk => ⟨2, ?_⟩⟩
  have hA : play 2 (GuardianBot k) (GuardianBot k) = some .C := by
    simpa using gg_guardian_C_vs_guardian k 0
  exact outcome_of_plays _ _ _ _ _ hA hA

end PD.Theorems


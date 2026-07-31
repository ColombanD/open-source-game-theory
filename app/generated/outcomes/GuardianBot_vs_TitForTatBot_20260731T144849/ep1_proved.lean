import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- GuardianBot plays C vs .bot CooperateBot (guard: CooperateBot plays D vs bot CB, refuted)
theorem gtft_guardian_botCB_guard_false (k : Nat) :
    proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_CooperateBot_plays_D_false _)
  | false => rfl

theorem gtft_GuardianBot_C_vs_botCB (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (.bot CooperateBot) = some .C := by
  have hg := gtft_guardian_botCB_guard_false k
  show eval (fuel + 2) (GuardianBot k) (.bot CooperateBot) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- TitForTatBot plays C vs GuardianBot: probe sees GuardianBot cooperate vs bot CB
theorem gtft_TFT_C_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (GuardianBot k) = some .C := by
  have hGuard : play (fuel + 2) (GuardianBot k) (.bot CooperateBot) = some .C :=
    gtft_GuardianBot_C_vs_botCB k fuel
  have hG : eval (fuel + 3) TitForTatBot (GuardianBot k) (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (GuardianBot k) CooperateBot Action.C hGuard
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (GuardianBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.C (by rfl) hG
  simpa [eval] using hPlay

-- GuardianBot plays C vs TitForTatBot: guard "TFT plays D vs bot CB" refuted
-- TFT plays C vs bot CB (cooperates against cooperator)
theorem gtft_TFT_C_vs_botCB (fuel : Nat) :
    play (fuel + 4) TitForTatBot (.bot CooperateBot) = some .C := by
  have hInner : play (fuel + 2) (.bot CooperateBot) (.bot CooperateBot) = some .C :=
    play_bot_CooperateBot fuel (.bot CooperateBot)
  have hG : eval (fuel + 3) TitForTatBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (.bot CooperateBot) CooperateBot Action.C hInner
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D) Action.C Action.C (by rfl) hG
  simpa [eval] using hPlay

theorem gtft_interp_TFT_D_vs_botCB_false :
    ¬ (Formula.plays TitForTatBot (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp only [play, eval, reduceCtorEq] at hn
  | succ m => cases m with
    | zero => simp [play, eval, TitForTatBot] at hn
    | succ m => cases m with
      | zero => simp [play, eval, TitForTatBot] at hn
      | succ m => cases m with
        | zero => simp [play, eval, TitForTatBot, Prog.subst, CooperateBot] at hn
        | succ fuel =>
            have hC : play (fuel + 4) TitForTatBot (.bot CooperateBot) = some .C :=
              gtft_TFT_C_vs_botCB fuel
            rw [show fuel + 1 + 1 + 1 + 1 = fuel + 4 by ring] at hn
            rw [hC] at hn; cases hn

theorem gtft_guardian_TFT_guard_false (k : Nat) :
    proofSearch k (.plays TitForTatBot (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays TitForTatBot (.bot CooperateBot) .D) with
  | true => exact absurd (proofSearch_sound _ _ h) gtft_interp_TFT_D_vs_botCB_false
  | false => rfl

theorem gtft_GuardianBot_C_vs_TFT (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) TitForTatBot = some .C := by
  have hg := gtft_guardian_TFT_guard_false k
  show eval (fuel + 2) (GuardianBot k) TitForTatBot (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_GuardianBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) TitForTatBot = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨4, ?_⟩⟩
  have hA : play 4 (GuardianBot k) TitForTatBot = some .C := by
    simpa using gtft_GuardianBot_C_vs_TFT k 2
  have hB : play 4 TitForTatBot (GuardianBot k) = some .C := by
    simpa using gtft_TFT_C_vs_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems


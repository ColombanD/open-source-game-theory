import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem PrudentBot_plays_D_against_bot_CB (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D := by
  show eval (fuel + 4) (PrudentBot k) (.bot CooperateBot) (PrudentBot k) = some .D
  have hCD : (Action.C == Action.D) = false := rfl
  simp [PrudentBot, CooperateBot, eval, Prog.subst, Formula.subst, hCD]

theorem TFT_plays_D_against_PrudentBot (k fuel : Nat) :
    play (fuel + 6) TitForTatBot (PrudentBot k) = some .D := by
  have hProbe : play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_against_bot_CB k fuel
  have hGuard :
      eval (fuel + 5) TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) TitForTatBot (PrudentBot k) CooperateBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 5 TitForTatBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_TitForTatBot_plays_C_against_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ n0 =>
  cases n0 with
  | zero => simp [play, eval, TitForTatBot] at hn
  | succ n1 =>
  cases n1 with
  | zero => simp [play, eval, TitForTatBot] at hn
  | succ n2 =>
  cases n2 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot] at hn
  | succ n3 =>
  cases n3 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot, DefectBot, Formula.subst] at hn
  | succ n4 =>
  cases n4 with
  | zero => simp [play, eval, TitForTatBot, PrudentBot, Prog.subst, CooperateBot, DefectBot, Formula.subst] at hn
  | succ fuel =>
    have hD : play (fuel + 6) TitForTatBot (PrudentBot k) = some .D :=
      TFT_plays_D_against_PrudentBot k fuel
    have heq : fuel + 1 + 1 + 1 + 1 + 1 + 1 = fuel + 6 := by omega
    rw [heq] at hn
    rw [hD] at hn
    cases hn

theorem proofSearch_false_for_TitForTatBot_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays TitForTatBot (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays TitForTatBot (PrudentBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h)
                         (interp_TitForTatBot_plays_C_against_PrudentBot_false k)
  | false => rfl

theorem PrudentBot_plays_D_against_TFT (k fuel : Nat) :
    play (fuel + 6) (PrudentBot k) TitForTatBot = some .D := by
  have hps := proofSearch_false_for_TitForTatBot_vs_PrudentBot k
  simp only [TitForTatBot, PrudentBot, CooperateBot, DefectBot] at hps
  show eval (fuel + 6) (PrudentBot k) TitForTatBot (PrudentBot k) = some .D
  have hDC : (Action.D == Action.C) = false := rfl
  simp [PrudentBot, TitForTatBot, CooperateBot, DefectBot, eval, Prog.subst, Formula.subst,
        hps, hDC]

theorem llm_outcome_PrudentBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) TitForTatBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) TitForTatBot = some .D :=
    PrudentBot_plays_D_against_TFT k 0
  have hB : play 6 TitForTatBot (PrudentBot k) = some .D :=
    TFT_plays_D_against_PrudentBot k 0
  simp [outcome, hA, hB]

end PD.Theorems

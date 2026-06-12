import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.DefectBot

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem PrudentBot_plays_D_vs_bot_CB (k fuel : Nat) :
    play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D := by
  have hProbe : play (fuel + 2) (.bot CooperateBot) (.bot DefectBot) = some .C := by
    show eval (fuel + 2) (.bot CooperateBot) (.bot DefectBot) (.bot CooperateBot) = some .C
    simp [eval, CooperateBot]
  have hGuard : eval (fuel + 3) (PrudentBot k) (.bot CooperateBot)
                  (.sim .opp (.bot DefectBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) (PrudentBot k) (.bot CooperateBot)
        DefectBot Action.C hProbe)
  have hPlay := play_ite_from_guard
    fuel 3 (PrudentBot k) (.bot CooperateBot) (.sim .opp (.bot DefectBot))
    (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem proofSearch_false_botDB_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (PrudentBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

theorem PrudentBot_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 5) (PrudentBot k) (.bot DefectBot) = some .D := by
  have hProbe : play (fuel + 2) (.bot DefectBot) (.bot DefectBot) = some .D := by
    show eval (fuel + 2) (.bot DefectBot) (.bot DefectBot) (.bot DefectBot) = some .D
    simp [eval, DefectBot]
  have hGuard : eval (fuel + 3) (PrudentBot k) (.bot DefectBot)
                  (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) (PrudentBot k) (.bot DefectBot)
        DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    (fuel + 1) 3 (PrudentBot k) (.bot DefectBot) (.sim .opp (.bot DefectBot))
    (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.D
    (by rfl) (by simpa [Nat.add_assoc] using hGuard)
  have hg := proofSearch_false_botDB_vs_PrudentBot k
  simp [eval, Prog.subst, Formula.subst, hg] at hPlay
  exact hPlay

theorem OBot_plays_D_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 6) OBot (PrudentBot k) = some .D := by
  have hPrudCB : play (fuel + 4) (PrudentBot k) (.bot CooperateBot) = some .D :=
    PrudentBot_plays_D_vs_bot_CB k fuel
  have hGuard : eval (fuel + 5) OBot (PrudentBot k)
                  (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) OBot (PrudentBot k)
        CooperateBot Action.D hPrudCB)
  have hPlay := play_ite_from_guard
    fuel 5 OBot (PrudentBot k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_OBot_plays_C_vs_PrudentBot_false (k : Nat) :
    ¬ (Formula.plays OBot (PrudentBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 6) OBot (PrudentBot k) = some .D :=
    OBot_plays_D_vs_PrudentBot k n
  have hC : play (n + 6) OBot (PrudentBot k) = some .C := by
    unfold play at hn ⊢
    exact eval_mono_le hn (n + 6) (by omega)
  rw [hC] at hD
  cases hD

theorem proofSearch_false_OBot_vs_PrudentBot (k : Nat) :
    proofSearch k (.plays OBot (PrudentBot k) .C) = false := by
  cases h : proofSearch k (.plays OBot (PrudentBot k) .C) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_OBot_plays_C_vs_PrudentBot_false k)
  | false => rfl

theorem OBot_plays_D_vs_bot_DB (fuel : Nat) :
    play (fuel + 4) OBot (.bot DefectBot) = some .D := by
  have hGuard : eval (fuel + 3) OBot (.bot DefectBot)
                  (.sim .opp (.bot CooperateBot)) = some .D := by
    simp [eval, Prog.subst, DefectBot]
  have hPlay := play_ite_from_guard
    fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem PrudentBot_plays_D_vs_OBot (k fuel : Nat) :
    play (fuel + 6) (PrudentBot k) OBot = some .D := by
  have hOBotDB : play (fuel + 4) OBot (.bot DefectBot) = some .D :=
    OBot_plays_D_vs_bot_DB fuel
  have hGuard : eval (fuel + 5) (PrudentBot k) OBot
                  (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 4) (PrudentBot k) OBot
        DefectBot Action.D hOBotDB)
  have hgsearch := proofSearch_false_OBot_vs_PrudentBot k
  have hPlay := play_ite_from_guard
    fuel 5 (PrudentBot k) OBot (.sim .opp (.bot DefectBot))
    (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.D Action.D
    (by rfl) hGuard
  simp [eval, Prog.subst, Formula.subst, hgsearch] at hPlay
  exact hPlay

theorem llm_outcome_PrudentBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) OBot = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨6, ?_⟩⟩
  have hA : play 6 (PrudentBot k) OBot = some .D := by
    simpa using PrudentBot_plays_D_vs_OBot k 0
  have hB : play 6 OBot (PrudentBot k) = some .D := by
    simpa using OBot_plays_D_vs_PrudentBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

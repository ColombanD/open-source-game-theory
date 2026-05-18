import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_OBot_vs_OBot (n : Nat) :
    outcome (n + 8) OBot OBot = some (.D, .D) := by
  -- Step 1: OBot plays C against (.bot CooperateBot)
  have hOBotC : play (n + 6) OBot (.bot CooperateBot) = some .C := by
    have hOuter : eval (n + 5) OBot (.bot CooperateBot)
        (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hInner : eval (n + 5) OBot (.bot CooperateBot)
        (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hPlay := play_ite_from_guard
      n 5 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by unfold OBot; rfl) hOuter
    simpa [eval, hInner] using hPlay
  -- Step 2: OBot plays D against (.bot DefectBot)
  have hOBotD : play (n + 6) OBot (.bot DefectBot) = some .D := by
    have hOuter : eval (n + 5) OBot (.bot DefectBot)
        (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hPlay := play_ite_from_guard
      n 5 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.D
      (by unfold OBot; rfl) hOuter
    simpa [eval] using hPlay
  -- Step 3: OBot vs OBot
  have hG1 : eval (n + 7) OBot OBot (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hOBotC
  have hG2 : eval (n + 7) OBot OBot (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hOBotD
  have hPlay := play_ite_from_guard
    n 7 OBot OBot (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by unfold OBot; rfl) hG1
  have hA : play (n + 8) OBot OBot = some .D := by
    simpa [eval, hG2] using hPlay
  exact outcome_of_plays _ _ _ _ _ hA hA

end PDNew.Theorems

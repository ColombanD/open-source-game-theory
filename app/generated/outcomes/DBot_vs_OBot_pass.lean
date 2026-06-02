import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_DBot_vs_OBot (n : Nat) :
    outcome (n+7) DBot OBot = some (.C, .D) := by
  -- DBot's leg: probe OBot vs DefectBot → OBot plays D → DBot cooperates
  have hOBotvsBotD_outer :
      eval (n + 4) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
    simp [eval, Prog.subst, DefectBot]
  have hOBotvsBotD : play (n + 5) OBot (.bot DefectBot) = some .D := by
    have hPlay := play_ite_from_guard
      n 4 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.D
      (by unfold OBot; rfl) hOBotvsBotD_outer
    simpa [eval] using hPlay
  have hGuard1 : eval (n + 6) DBot OBot (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hOBotvsBotD
  have hA : play (n + 7) DBot OBot = some .C := by
    have hPlay := play_ite_from_guard
      n 6 DBot OBot (.sim .opp (.bot DefectBot))
      (.const Action.D) (.const Action.C)
      Action.C Action.D
      (by rfl) hGuard1
    simpa [eval] using hPlay
  -- OBot's leg: probe DBot vs CooperateBot → DBot plays D → OBot defects
  have hDBotvsBotC_outer :
      eval (n + 4) DBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
    simp [eval, Prog.subst, CooperateBot]
  have hDBotvsBotC : play (n + 5) DBot (.bot CooperateBot) = some .D := by
    have hPlay := play_ite_from_guard
      n 4 DBot (.bot CooperateBot) (.sim .opp (.bot DefectBot))
      (.const Action.D) (.const Action.C)
      Action.C Action.C
      (by unfold DBot; rfl) hDBotvsBotC_outer
    simpa [eval] using hPlay
  have hGuard2 : eval (n + 6) OBot DBot (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hDBotvsBotC
  have hB : play (n + 7) OBot DBot = some .D := by
    have hPlay := play_ite_from_guard
      n 6 OBot DBot (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.D
      (by rfl) hGuard2
    simpa [eval] using hPlay
  exact outcome_of_plays _ _ _ _ _ hA hB

end PDNew.Theorems

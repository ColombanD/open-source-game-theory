import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_OBot_vs_TitForTatBot (n : Nat) :
    outcome (n+7) OBot TitForTatBot = some (.D, .C) := by
  have hGuard1 : eval (n + 6) OBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
    simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
  have hGuard2 : eval (n + 6) OBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
    simp [eval, Prog.subst, TitForTatBot, DefectBot, CooperateBot]; decide
  have hA : play (n + 7) OBot TitForTatBot = some .D := by
    have hPlay := play_ite_from_guard
        n 6 OBot TitForTatBot (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.C
        (by rfl) hGuard1
    simpa [eval, hGuard2] using hPlay
  have hGuard3 : eval (n + 6) TitForTatBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
    simp [eval, Prog.subst, OBot, CooperateBot]; decide
  have hB : play (n + 7) TitForTatBot OBot = some .C := by
    have hPlay := play_ite_from_guard
        n 6 TitForTatBot OBot (.sim .opp (.bot CooperateBot))
        (.const Action.C) (.const Action.D)
        Action.C Action.C
        (by rfl) hGuard3
    simpa [eval] using hPlay
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

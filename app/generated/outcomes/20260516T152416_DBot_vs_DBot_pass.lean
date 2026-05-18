import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_DBot_vs_DBot (n : Nat) :
    outcome (n + 7) DBot DBot = some (.D, .D) := by
  have hGuard : eval (n + 6) DBot DBot (.sim .opp (.bot DefectBot)) = some .C := by
    simp [eval, Prog.subst, DBot, DefectBot]; decide
  have hA : play (n + 7) DBot DBot = some .D := by
    have hPlay := play_ite_from_guard
        n 6 DBot DBot (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C)
        Action.C Action.C
        (by rfl) hGuard
    simpa [eval] using hPlay
  exact outcome_of_plays _ _ _ _ _ hA hA

end PDNew.Theorems

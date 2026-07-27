import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers

open PD.Bots
namespace PD.Theorems
theorem outcome_DBot_vs_DBot (fuel : Nat):
    outcome (fuel + 6) DBot DBot = some (.D, .D) := by
    -- After substitution, the outer guard reduces to running DBot with
    -- opponent (.bot DefectBot) — not DefectBot — because `.bot` blocks
    -- subst. So we directly trace DBot vs (.bot DefectBot).
    have hInnerGuard :
        eval (fuel + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hInner : eval (fuel + 4) DBot (.bot DefectBot) DBot = some .C := by
      have hPlay := play_ite_from_guard
        fuel 3 DBot (.bot DefectBot) (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C)
        Action.C Action.D
        (by unfold DBot; rfl) hInnerGuard
      simpa [play, eval] using hPlay
    have hOuterGuard :
        eval (fuel + 5) DBot DBot (.sim .opp (.bot DefectBot)) = some .C := by
      rw [show eval (fuel + 5) DBot DBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 4) DBot (.bot DefectBot) DBot by rfl]
      exact hInner
    have hA : play (fuel + 6) DBot DBot = some .D := by
      have hPlay := play_ite_from_guard
        fuel 5 DBot DBot (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C)
        Action.C Action.C
        (by rfl) hOuterGuard
      simpa [eval] using hPlay
    simp [outcome, hA]

end PD.Theorems

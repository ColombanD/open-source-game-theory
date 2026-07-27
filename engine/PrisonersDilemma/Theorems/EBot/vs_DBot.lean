import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_DBot (fuel : Nat):
    outcome (fuel + 8) EBot DBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 7) EBot DBot (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, DBot, DefectBot]; decide
    have hA : play (fuel + 8) EBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 7 EBot DBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 7) DBot EBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, EBot, DefectBot, CooperateBot, MirrorBot]; decide
    have hB : play (fuel + 8) DBot EBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 7 DBot EBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

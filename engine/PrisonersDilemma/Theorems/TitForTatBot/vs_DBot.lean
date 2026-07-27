import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_TitForTatBot_vs_DBot (fuel : Nat):
    outcome (fuel + 6) TitForTatBot DBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 5) TitForTatBot DBot (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DBot, CooperateBot, DefectBot]; decide
    have hGuard2 : eval (fuel + 5) DBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot, DefectBot]; decide
    have hA : play (fuel + 6) TitForTatBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 5 TitForTatBot DBot (.sim .opp (.bot CooperateBot))
            (.const Action.C) (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval] using hPlay
    have hB : play (fuel + 6) DBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 5 DBot TitForTatBot (.sim .opp (.bot DefectBot))
            (.const Action.D) (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay
    simp [outcome, hA, hB]

end PD.Theorems

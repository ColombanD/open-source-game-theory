import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_TitForTatBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 6) TitForTatBot TitForTatBot = some (.C, .C) := by
    have hGuard : eval (fuel + 5) TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hA : play (fuel + 6) TitForTatBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 5 TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot))
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        simpa [eval] using hPlay
    simp [outcome, hA]

end PD.Theorems

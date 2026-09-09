import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_TitForTatBot_vs_TitForTatBot :
    OutcomeSpec .nobudget 6
      (fun _ => TitForTatBot) (fun _ => TitForTatBot) (some (.C, .C)) := by
    intro fuel
    have hGuard : eval (fuel + 5) TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hA : play (fuel + 6) TitForTatBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 5 TitForTatBot TitForTatBot (.sim .opp (.bot CooperateBot))
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        simpa [eval] using! hPlay
    simp [outcome, hA]

end PD.Theorems

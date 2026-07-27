import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_OBot_vs_DBot (fuel : Nat):
    outcome (fuel + 6) OBot DBot = some (.D, .C) := by
    -- hGuard1: simulates DBot vs (.bot CooperateBot). DBot's inner guard
    -- returns C, so DBot takes its const-D branch.
    have hGuard1 : eval (fuel + 5) OBot DBot (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DBot, CooperateBot, DefectBot]; decide
    -- hGuard2: simulates OBot vs (.bot DefectBot). OBot's outer guard returns
    -- D, so OBot takes its const-D else-branch.
    have hG2Outer : eval (fuel + 3) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotDefect : play (fuel + 4) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hG2Outer
      simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 5) DBot OBot (.sim .opp (.bot DefectBot)) = some .D := by
      rw [show eval (fuel + 5) DBot OBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 4) OBot (.bot DefectBot) OBot by rfl]
      simpa [play] using hOBotvsBotDefect

    have hA : play (fuel + 6) OBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 5 OBot DBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval] using hPlay

    have hB : play (fuel + 6) DBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 5 DBot OBot (.sim .opp (.bot DefectBot))
            (.const Action.D) (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay

    simp [outcome, hA, hB]

end PD.Theorems

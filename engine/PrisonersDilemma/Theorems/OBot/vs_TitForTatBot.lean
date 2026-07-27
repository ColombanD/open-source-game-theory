import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_OBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) OBot TitForTatBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 6) OBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hGuard2 : eval (fuel + 6) OBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot, DefectBot]; decide
    have hA : play (fuel + 7) OBot TitForTatBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 OBot TitForTatBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    have hB : play (fuel + 7) TitForTatBot OBot = some .C := by
        -- TitForTatBot's guard reduces to OBot vs (.bot CooperateBot). We trace
        -- OBot's outer ite (guard = C → take then-branch which is inner ite,
        -- inner guard = C → take const C).
        have hOuter : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
          simp [eval, Prog.subst, CooperateBot]
        have hInner : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
          simp [eval, Prog.subst, CooperateBot]
        have hOBot : play (fuel + 5) OBot (.bot CooperateBot) = some .C := by
          have hPlay := play_ite_from_guard
            fuel 4 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by unfold OBot; rfl) hOuter
          simpa [eval, hInner] using hPlay
        have hGuard : eval (fuel + 6) TitForTatBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
          rw [show eval (fuel + 6) TitForTatBot OBot (.sim .opp (.bot CooperateBot)) =
                  eval (fuel + 5) OBot (.bot CooperateBot) OBot by rfl]
          simpa [play] using hOBot
        have hPlay := play_ite_from_guard
            fuel 6 TitForTatBot OBot (.sim .opp (.bot CooperateBot))
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        exact hPlay ▸ rfl
    unfold outcome
    rw [hA, hB]
    rfl

end PD.Theorems

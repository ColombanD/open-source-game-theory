import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_OBot_vs_OBot (fuel : Nat):
    outcome (fuel + 7) OBot OBot = some (.D, .D) := by
    -- After substitution, OBot's outer guard simulates OBot vs (.bot CooperateBot).
    -- Trace OBot's outer ite (guard = C, take then-branch = inner ite, inner
    -- guard = C, take const C) → some C.
    have hOuter : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hInner : eval (fuel + 4) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotCB : play (fuel + 5) OBot (.bot CooperateBot) = some .C := by
      have hPlay := play_ite_from_guard
        fuel 4 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.C
        (by unfold OBot; rfl) hOuter
      simpa [eval, hInner] using hPlay
    have hGuard1 : eval (fuel + 6) OBot OBot (.sim .opp (.bot CooperateBot)) = some .C := by
      rw [show eval (fuel + 6) OBot OBot (.sim .opp (.bot CooperateBot)) =
              eval (fuel + 5) OBot (.bot CooperateBot) OBot by rfl]
      simpa [play] using hOBotvsBotCB

    -- Same idea for the inner guard: simulates OBot vs (.bot DefectBot),
    -- where OBot's outer guard returns D, so falls to const D.
    have hOuterD : eval (fuel + 3) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotDB : play (fuel + 4) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 3 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hOuterD
      simpa [eval] using hPlay
    have hGuard2 : eval (fuel + 6) OBot OBot (.sim .opp (.bot DefectBot)) = some .D := by
      rw [show eval (fuel + 6) OBot OBot (.sim .opp (.bot DefectBot)) =
              eval (fuel + 5) OBot (.bot DefectBot) OBot by rfl]
      simpa [play] using hOBotvsBotDB

    have hA : play (fuel + 7) OBot OBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 OBot OBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay

    simp [outcome, hA]

end PD.Theorems

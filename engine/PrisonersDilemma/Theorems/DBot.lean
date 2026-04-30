import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers

open PDNew.Bots
namespace PDNew.Theorems

theorem DBot_plays_D_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) DBot CooperateBot = some .D := by
    apply play_from_eval
    unfold DBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem DBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) DBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot DBot = some .C := rfl
    simp [outcome, hA, hB]

theorem DBot_plays_C_against_DefectBot (fuel : Nat) :
    play (fuel + 3) DBot DefectBot = some .C := by
    apply play_from_eval
    unfold DBot DefectBot
    simp [eval, Prog.subst]
    decide

theorem DBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 3) DBot DefectBot = some (.C, .D) := by
    have hA : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DefectBot (fuel)
    have hB : play (fuel + 3) DefectBot DBot = some .D := rfl
    simp [outcome, hA, hB]


theorem DBot_vs_DBot (fuel : Nat):
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

end PDNew.Theorems

import PrisonersDilemmaNew.Bots.DBot
import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.DefectBot
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.DefectBot
import PrisonersDilemmaNew.Theorems.Helpers

open PDNew.Bots
namespace PDNew.Theorems

theorem DBot_plays_D_against_CB (fuel : Nat) :
    play (fuel + 3) DBot CooperateBot = some .D := by
    apply play_from_eval
    unfold DBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem DBot_vs_CB (fuel : Nat):
    outcome (fuel + 3) DBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CB (fuel)
    have hB : play (fuel + 3) CooperateBot DBot = some .C := rfl
    simp [outcome, hA, hB]

theorem DBot_plays_C_against_DB (fuel : Nat) :
    play (fuel + 3) DBot DefectBot = some .C := by
    apply play_from_eval
    unfold DBot DefectBot
    simp [eval, Prog.subst]
    decide

theorem DBot_vs_DB (fuel : Nat):
    outcome (fuel + 3) DBot DefectBot = some (.C, .D) := by
    have hA : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot DBot = some .D := rfl
    simp [outcome, hA, hB]


theorem DBot_vs_DBot (fuel : Nat):
    outcome (fuel + 5) DBot DBot = some (.D, .D) := by
    have hProbe : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DB (fuel)
    have hGuard : eval (fuel + 4) DBot DBot (.sim .opp DefectBot) = some .C := by
        simpa [eval, Prog.subst, play] using hProbe
    have hA : play (fuel + 5) DBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 4 DBot DBot (.sim .opp DefectBot)
            (.const Action.D) (.const Action.C)
            Action.C Action.C
            (by rfl) hGuard
        simpa [eval] using hPlay
    simp [outcome, hA]

end PDNew.Theorems

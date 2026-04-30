import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.Helpers


open PDNew.Bots
namespace PDNew.Theorems


theorem TitForTatBot_plays_C_against_CB (fuel : Nat) :
    play (fuel + 3) TitForTatBot CooperateBot = some .C := by
    apply play_from_eval
    unfold TitForTatBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem TitForTatBot_vs_CB (fuel : Nat):
    outcome (fuel + 3) TitForTatBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 3) TitForTatBot CooperateBot = some .C := TitForTatBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 3) CooperateBot TitForTatBot = some .C := rfl
    simp [outcome, hA, hB]

theorem TitForTatBot_plays_D_against_DB (fuel : Nat) :
    play (fuel + 3) TitForTatBot DefectBot = some .D := by
    apply play_from_eval
    unfold TitForTatBot DefectBot
    simp [eval, Prog.subst]
    decide

theorem TitForTatBot_vs_DB (fuel : Nat):
    outcome (fuel + 3) TitForTatBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) TitForTatBot DefectBot = some .D := TitForTatBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot TitForTatBot = some .D := rfl
    simp [outcome, hA, hB]


theorem TitForTatBot_vs_TitForTatBot (fuel : Nat):
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

theorem TitForTatBot_vs_DBot (fuel : Nat):
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

end PDNew.Theorems

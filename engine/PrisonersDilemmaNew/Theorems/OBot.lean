import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.DefectBot
import PrisonersDilemmaNew.Bots.TitForTatBot
import PrisonersDilemmaNew.Bots.OBot
import PrisonersDilemmaNew.Theorems.DBot
import PrisonersDilemmaNew.Theorems.TitForTatBot
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.Helpers


open PDNew.Bots
namespace PDNew.Theorems


theorem OBot_plays_C_against_CB(fuel : Nat) :
    play (fuel + 5) OBot CooperateBot = some .C := by
    apply play_from_eval
    unfold OBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem OBot_vs_CB (fuel : Nat):
    outcome (fuel + 5) OBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 5) OBot CooperateBot = some .C := OBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 5) CooperateBot OBot = some .C := rfl
    simp [outcome, hA, hB]

theorem OBot_plays_D_against_DB (fuel : Nat) :
    play (fuel + 3) OBot DefectBot = some .D := by
    have hGuard : eval (fuel + 2) OBot DefectBot (.sim .opp CooperateBot) = some .D := by
        unfold OBot DefectBot CooperateBot
        simp [eval, Prog.subst]
    have hPlay := play_ite_from_guard
        fuel 2 OBot DefectBot (.sim .opp CooperateBot)
        (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by rfl) hGuard
    simpa [eval] using hPlay

theorem OBot_vs_DB (fuel : Nat):
    outcome (fuel + 3) OBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot OBot = some .D := rfl
    simp [outcome, hA, hB]


theorem OBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 9) OBot TitForTatBot = some (.D, .C) := by
    have hGuard1 : eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) = some .C := by
        have hProbe : play (fuel + 7) TitForTatBot CooperateBot = some .C :=
            (TitForTatBot_plays_C_against_CB (fuel + 4)) ▸ rfl
        show eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) = some .C
        rw [show eval (fuel + 8) OBot TitForTatBot (.sim .opp CooperateBot) =
                eval (fuel + 7) TitForTatBot CooperateBot TitForTatBot by rfl]
        simp only [show eval (fuel + 7) TitForTatBot CooperateBot TitForTatBot =
                        play (fuel + 7) TitForTatBot CooperateBot by rfl]
        exact hProbe
    have hA : play (fuel + 9) OBot TitForTatBot = some .D := by
        have hGuard2 : eval (fuel + 7) OBot TitForTatBot (.sim .opp DefectBot) = some .D := by
            have hProbe : play (fuel + 6) TitForTatBot DefectBot = some .D :=
                (TitForTatBot_plays_D_against_DB (fuel + 3)) ▸ rfl
            show eval (fuel + 7) OBot TitForTatBot (.sim .opp DefectBot) = some .D
            rw [show eval (fuel + 7) OBot TitForTatBot (.sim .opp DefectBot) =
                    eval (fuel + 6) TitForTatBot DefectBot TitForTatBot by rfl]
            simp only [show eval (fuel + 6) TitForTatBot DefectBot TitForTatBot =
                            play (fuel + 6) TitForTatBot DefectBot by rfl]
            exact hProbe
        -- Apply outer ite helper: play (fuel+9) OBot = ...conditional...
        have hOuterIte := play_ite_from_guard
            fuel 8 OBot TitForTatBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard1
        -- Simplify using the outer conditional result
        rw [hOuterIte]
        -- The if condition (Action.C == Action.C) = true is trivially true
        have : (Action.C : PDNew.Action) == Action.C = true := by rfl
        rw [this]
        -- Now simplify and use hGuard2 to finish
        simp_all only []
    have hB : play (fuel + 9) TitForTatBot OBot = some .C := by
        have hProbe : play (fuel + 7) OBot CooperateBot = some .C :=
            (OBot_plays_C_against_CB (fuel + 2)) ▸ rfl
        have hGuard : eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) = some .C := by
            show eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) = some .C
            rw [show eval (fuel + 8) TitForTatBot OBot (.sim .opp CooperateBot) =
                    eval (fuel + 7) OBot CooperateBot OBot by rfl]
            simp only [show eval (fuel + 7) OBot CooperateBot OBot =
                            play (fuel + 7) OBot CooperateBot by rfl]
            exact hProbe
        have hPlay := play_ite_from_guard
            fuel 8 TitForTatBot OBot (.sim .opp CooperateBot)
            (.const Action.C) (.const Action.D)
            Action.C Action.C
            (by rfl) hGuard
        exact hPlay ▸ rfl
    unfold outcome
    rw [hA, hB]
    rfl

theorem OBot_vs_DBot (fuel : Nat):
    outcome (fuel + 5) OBot DBot = some (.D, .C) := by
    have hProbe1 : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB fuel
    have hProbe2 : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CB fuel
    have hGuard1 : eval (fuel + 4) OBot DBot (.sim .opp CooperateBot) = some .D := by
        simpa [eval, Prog.subst, play] using hProbe1
    have hGuard2 : eval (fuel + 4) DBot OBot (.sim .opp DefectBot) = some .D := by
        simpa [eval, Prog.subst, play] using hProbe2
    have hA : play (fuel + 5) OBot DBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 4 OBot DBot (.sim .opp CooperateBot)
            (.ite (.sim .opp DefectBot) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval] using hPlay
    have hB : play (fuel + 5) DBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 4 DBot OBot (.sim .opp DefectBot)
            (.const Action.D) (.const Action.C)
            Action.C Action.D
            (by rfl) hGuard2
        simpa [eval] using hPlay
    simp [outcome, hA, hB]


theorem OBot_vs_Obot

end PDNew.Theorems

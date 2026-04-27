import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.TitForTatBot


open PDNew.Bots
namespace PDNew.Theorems

theorem EBot_plays_D_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) EBot CooperateBot = some .D := by
    apply play_from_eval
    unfold EBot CooperateBot
    simp [eval, Prog.subst]
    intro h
    have : (Action.C == Action.C) = true := by decide
    simp [this] at h

theorem EBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) EBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot EBot = some .C := rfl
    simp [outcome, hA, hB]

theorem EBot_plays_D_against_DefectBot (fuel : Nat) :
    play (fuel + 5) EBot DefectBot = some .D := by
    apply play_from_eval
    unfold EBot DefectBot
    simp [eval, Prog.subst]
    intro h
    simp [h]

theorem EBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 5) EBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 5) EBot DefectBot = some .D := EBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 5) DefectBot EBot = some .D := rfl
    simp [outcome, hA, hB]

theorem EBot_vs_Dbot (fuel : Nat):
    outcome (fuel + 7) EBot DBot = some (.D, .C) := by
    have hA : play (fuel + 7) EBot DBot = some .D := EBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 7) DBot EBot = some .C := DBot_plays_C_against_DefectBot (fuel)
    simp [outcome, hA, hB]

theorem EBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) EBot TitForTatBot = some (.C, .D) := by
    have hGuard1 : eval (fuel + 6) EBot TitForTatBot (.sim .opp DefectBot) = some .D := by
        have hProbe : play (fuel + 5) TitForTatBot DefectBot = some .D :=
            (TitForTatBot_plays_D_against_DB (fuel + 2)) ▸ rfl
        rw [show eval (fuel + 6) EBot TitForTatBot (.sim .opp DefectBot) =
                eval (fuel + 5) TitForTatBot DefectBot TitForTatBot by rfl]
        rw [show eval (fuel + 5) TitForTatBot DefectBot TitForTatBot =
                        play (fuel + 5) TitForTatBot DefectBot by rfl]
        exact hProbe
    have hGuard2 : eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) = some .C := by
        have hProbe : play (fuel + 5) TitForTatBot CooperateBot = some .C :=
            (TitForTatBot_plays_C_against_CB (fuel + 2)) ▸ rfl
        show eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) = some .C
        rw [show eval (fuel + 6) EBot TitForTatBot (.sim .opp CooperateBot) =
                eval (fuel + 5) TitForTatBot CooperateBot TitForTatBot by rfl]
        rw [show eval (fuel + 5) TitForTatBot CooperateBot TitForTatBot =
                        play (fuel + 5) TitForTatBot CooperateBot by rfl]
        exact hProbe
    have hA : play (fuel + 7) EBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot TitForTatBot (.sim .opp DefectBot)
            (.const Action.D)
            (.ite (.sim .opp CooperateBot) Action.C (.const Action.C) (.ite (.sim .opp MirrorBot) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay

    have hB : play (fuel + 7) TitForTatBot EBot = some .D := rfl
    simp [outcome, hA, hB]

end PDNew.Theorems

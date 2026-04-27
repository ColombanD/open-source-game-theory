import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Theorems.Helpers


open PDNew.Bots
namespace PDNew.Theorems

theorem MirrorBot_plays_C_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) MirrorBot CooperateBot = some .C := by
    apply play_from_eval
    unfold MirrorBot CooperateBot
    simp [eval, Prog.subst]

theorem MirrorBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) MirrorBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 3) MirrorBot CooperateBot = some .C := MirrorBot_plays_C_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot MirrorBot = some .C := rfl
    simp [outcome, hA, hB]

theorem MirrorBot_plays_D_against_DefectBot (fuel : Nat) :
    play (fuel + 3) MirrorBot DefectBot = some .D := by
    apply play_from_eval
    unfold MirrorBot DefectBot
    simp [eval, Prog.subst]

theorem MirrorBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 3) MirrorBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) MirrorBot DefectBot = some .D := MirrorBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 3) DefectBot MirrorBot = some .D := rfl
    simp [outcome, hA, hB]

/-- DBot cooperates against MirrorBot: DBot's defect-probe asks whether the
    opponent (MirrorBot) cooperates against DefectBot. MirrorBot mirrors
    DefectBot and defects, so the probe returns `D ≠ C` and DBot falls through
    to its cooperate branch. -/
private theorem DBot_plays_C_against_MirrorBot (fuel : Nat) :
    play (fuel + 5) DBot MirrorBot = some .C := by
    have hProbe : play (fuel + 3) MirrorBot DefectBot = some .D :=
        MirrorBot_plays_D_against_DefectBot (fuel)
    have hGuard : eval (fuel + 4) DBot MirrorBot (.sim .opp DefectBot) = some .D := by
        simpa [eval, Prog.subst, play] using hProbe
    have hPlay := play_ite_from_guard
        fuel 4 DBot MirrorBot (.sim .opp DefectBot)
        (.const Action.D) (.const Action.C)
        Action.C Action.D
        (by rfl) hGuard
    simpa [eval] using hPlay

theorem MirrorBot_plays_C_against_DBot (fuel : Nat) :
    play (fuel + 6) MirrorBot DBot = some .C := by
    have hDBotPlays : play (fuel + 5) DBot MirrorBot = some .C :=
        DBot_plays_C_against_MirrorBot (fuel)
    simpa [play, eval, Prog.subst, MirrorBot] using hDBotPlays

theorem MirrorBot_vs_DBot (fuel : Nat):
    outcome (fuel + 6) MirrorBot DBot = some (.C, .C) := by
    have hA : play (fuel + 6) MirrorBot DBot = some .C := MirrorBot_plays_C_against_DBot (fuel)
    have hB : play (fuel + 6) DBot MirrorBot = some .C := DBot_plays_C_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PDNew.Theorems

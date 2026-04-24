import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
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

end PDNew.Theorems

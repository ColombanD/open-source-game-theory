import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers


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

end PDNew.Theorems

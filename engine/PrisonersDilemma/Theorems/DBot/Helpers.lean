import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Base.Helpers

open PD.Bots
namespace PD.Theorems
theorem DBot_plays_D_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) DBot CooperateBot = some .D := by
    apply play_from_eval
    unfold DBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem DBot_plays_C_against_DefectBot (fuel : Nat) :
    play (fuel + 3) DBot DefectBot = some .C := by
    apply play_from_eval
    unfold DBot DefectBot
    simp [eval, Prog.subst]
    decide

end PD.Theorems

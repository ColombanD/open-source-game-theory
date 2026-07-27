import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers


open PD.Bots
namespace PD.Theorems
theorem TitForTatBot_plays_C_against_CB (fuel : Nat) :
    play (fuel + 3) TitForTatBot CooperateBot = some .C := by
    apply play_from_eval
    unfold TitForTatBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem TitForTatBot_plays_D_against_DB (fuel : Nat) :
    play (fuel + 3) TitForTatBot DefectBot = some .D := by
    apply play_from_eval
    unfold TitForTatBot DefectBot
    simp [eval, Prog.subst]
    decide

end PD.Theorems

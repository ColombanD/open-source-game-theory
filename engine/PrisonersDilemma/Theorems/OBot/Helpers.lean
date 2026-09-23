import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers


open PD.Bots
namespace PD.Theorems
theorem OBot_plays_C_against_CB(fuel : Nat) :
    play (fuel + 5) OBot CooperateBot = some .C := by
    apply play_from_eval
    unfold OBot CooperateBot
    simp [eval, Prog.subst]
    decide

theorem OBot_plays_D_against_DB (fuel : Nat) :
    play (fuel + 3) OBot DefectBot = some .D := by
    have hGuard : eval (fuel + 2) OBot DefectBot (.sim .opp (.bot CooperateBot)) = some .D := by
        unfold OBot DefectBot CooperateBot
        simp [eval, Prog.subst]
    have hPlay := play_ite_from_guard
        fuel 2 OBot DefectBot (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by rfl) hGuard
    simpa [eval] using hPlay

end PD.Theorems

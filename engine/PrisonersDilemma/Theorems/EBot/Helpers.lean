import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.OBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot


open PD.Bots
namespace PD.Theorems
theorem EBot_plays_D_against_CooperateBot (fuel : Nat) :
    play (fuel + 3) EBot CooperateBot = some .D := by
    apply play_from_eval
    unfold EBot CooperateBot
    simp [eval, Prog.subst]
    intro h
    have : (Action.C == Action.C) = true := by decide
    simp [this] at h

theorem EBot_plays_D_against_DefectBot (fuel : Nat) :
    play (fuel + 5) EBot DefectBot = some .D := by
    apply play_from_eval
    unfold EBot DefectBot
    simp [eval, Prog.subst]
    intro h
    simp [h]

theorem EBot_plays_C_against_MirrorBot (fuel : Nat) :
    play (fuel + 7) EBot MirrorBot = some .C := by
    have hGuard1 : eval (fuel + 6) EBot MirrorBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, MirrorBot, DefectBot]
    have hGuard2 : eval (fuel + 6) EBot MirrorBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, MirrorBot, CooperateBot]
    have hPlay := play_ite_from_guard
        fuel 6 EBot MirrorBot (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.D
        (by rfl) hGuard1
    simpa [eval, hGuard2] using hPlay

end PD.Theorems

import PrisonersDilemmaNew.Bots.DBot
import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.DefectBot
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.DefectBot

open PDNew.Bots
namespace PDNew.Theorems

theorem DBot_vs_CB (fuel : Nat):
    outcome (fuel + 3) DBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) DBot CooperateBot = some .D := by
        show eval (fuel + 3) DBot CooperateBot DBot = some .D
        unfold DBot CooperateBot
        simp [eval, Prog.subst]
        decide
    have hB : play (fuel + 3) CooperateBot DBot = some .C := rfl
    simp [outcome, hA, hB]

theorem DBot_plays_C_against_DB (fuel : Nat) :
    play (fuel + 3) DBot DefectBot = some .C := by
    have hA : play (fuel + 3) DBot DefectBot = some .C := by
        show eval (fuel + 3) DBot DefectBot DBot = some .C
        unfold DBot DefectBot
        simp [eval, Prog.subst]
        decide
    simp [hA]

theorem DBot_vs_DB (fuel : Nat):
    outcome (fuel + 3) DBot DefectBot = some (.C, .D) := by
    have hA : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DB (fuel + 3)
    have hB : play (fuel + 3) DefectBot DBot = some .D := by
        rw [show fuel + 3 = (fuel + 2) + 1 from by omega]
        exact play_DefectBot (fuel + 2) DBot
    simp [outcome, hA, hB]


theorem DBot_vs_DBot (fuel : Nat):
    outcome (fuel + 5) DBot DBot = some (.D, .D) := by
    have hProbe : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DB (fuel)
    have hGuard : eval (fuel + 4) DBot DBot (.sim .opp DefectBot) = some .C := by
        simpa [eval, Prog.subst, play] using hProbe
    have hA : play (fuel + 5) DBot DBot = some .D := by
        unfold play
        change eval (fuel + 5) DBot DBot
            (.ite (.sim .opp DefectBot) Action.C (.const Action.D) (.const Action.C)) = some .D
        rw [show eval (fuel + 5) DBot DBot
                (.ite (.sim .opp DefectBot) Action.C (.const Action.D) (.const Action.C))
                =
                    (do
                        let r ← eval (fuel + 4) DBot DBot (.sim .opp DefectBot)
                        if r == Action.C then
                            eval (fuel + 4) DBot DBot (.const Action.D)
                        else
                            eval (fuel + 4) DBot DBot (.const Action.C)) by
                rfl]
        rw [hGuard]
        simp [eval]
        decide
    have hB : play (fuel + 5) DBot DBot = some .D := hA
    simp [outcome, hA]

end PDNew.Theorems

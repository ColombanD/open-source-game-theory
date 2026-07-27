import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.Helpers
import PrisonersDilemma.Theorems.OBot.vs_CooperateBot
import PrisonersDilemma.Theorems.OBot.vs_DBot
import PrisonersDilemma.Theorems.OBot.vs_DefectBot
import PrisonersDilemma.Theorems.OBot.vs_OBot
import PrisonersDilemma.Theorems.OBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.vs_CooperateBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_DefectBot
import PrisonersDilemma.Theorems.TitForTatBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Theorems.MirrorBot.vs_CooperateBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DBot
import PrisonersDilemma.Theorems.MirrorBot.vs_DefectBot
import PrisonersDilemma.Theorems.MirrorBot.vs_MirrorBot
import PrisonersDilemma.Theorems.MirrorBot.vs_OBot
import PrisonersDilemma.Theorems.MirrorBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 7) EBot TitForTatBot = some (.C, .D) := by
    have hGuard1 : eval (fuel + 6) EBot TitForTatBot (.sim .opp (.bot DefectBot)) = some .D := by
      simp [eval, Prog.subst, TitForTatBot, DefectBot, CooperateBot]; decide
    have hGuard2 : eval (fuel + 6) EBot TitForTatBot (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, TitForTatBot, CooperateBot]; decide
    have hA : play (fuel + 7) EBot TitForTatBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 6 EBot TitForTatBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    -- hGuard3 reduces to "EBot vs (.bot CooperateBot)". EBot's outer guard
    -- sees (.bot CooperateBot) cooperate against DefectBot, so it defects.
    have hOuterCB : eval (fuel + 4) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hEBotBotCB : play (fuel + 5) EBot (.bot CooperateBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 4 EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.C
        (by unfold EBot; rfl) hOuterCB
      simpa [eval] using hPlay
    have hGuard3 : eval (fuel + 6) TitForTatBot EBot (.sim .opp (.bot CooperateBot)) = some .D :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hEBotBotCB
    have hB : play (fuel + 7) TitForTatBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 6 TitForTatBot EBot (.sim .opp (.bot CooperateBot))
            (.const Action.C)
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

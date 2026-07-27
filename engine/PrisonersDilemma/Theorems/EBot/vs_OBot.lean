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
theorem outcome_EBot_vs_OBot (fuel : Nat):
    outcome (fuel + 8) EBot OBot = some (.C, .D) := by
    -- For hGuard1 we directly trace OBot vs (.bot DefectBot): OBot's outer
    -- guard returns D (since (.bot DefectBot) defects against CooperateBot),
    -- so OBot defects.
    have hOBotvsBotD_outer : eval (fuel + 5) OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot)) = some .D := by
      simp [eval, Prog.subst, DefectBot]
    have hOBotvsBotD : play (fuel + 6) OBot (.bot DefectBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 5 OBot (.bot DefectBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.D
        (by unfold OBot; rfl) hOBotvsBotD_outer
      simpa [eval] using hPlay
    have hGuard1 : eval (fuel + 7) EBot OBot (.sim .opp (.bot DefectBot)) = some .D :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hOBotvsBotD
    -- hGuard2 traces OBot vs (.bot CooperateBot): outer guard C, take inner ite
    -- whose guard is also C, take const C.
    have hOBotvsBotC_outer : eval (fuel + 5) OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotC_inner : eval (fuel + 5) OBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hOBotvsBotC : play (fuel + 6) OBot (.bot CooperateBot) = some .C := by
      have hPlay := play_ite_from_guard
        fuel 5 OBot (.bot CooperateBot) (.sim .opp (.bot CooperateBot))
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)
        Action.C Action.C
        (by unfold OBot; rfl) hOBotvsBotC_outer
      simpa [eval, hOBotvsBotC_inner] using hPlay
    have hGuard2 : eval (fuel + 7) EBot OBot (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hOBotvsBotC
    have hA : play (fuel + 8) EBot OBot = some .C := by
        have hPlay := play_ite_from_guard
            fuel 7 EBot OBot (.sim .opp (.bot DefectBot))
            (.const Action.D)
            (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
            Action.C Action.D
            (by rfl) hGuard1
        simpa [eval, hGuard2] using hPlay
    -- For hGuard3: EBot vs (.bot CooperateBot) — outer guard returns C, defect.
    have hEBotBotCB_outer : eval (fuel + 5) EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot)) = some .C := by
      simp [eval, Prog.subst, CooperateBot]
    have hEBotBotCB : play (fuel + 6) EBot (.bot CooperateBot) = some .D := by
      have hPlay := play_ite_from_guard
        fuel 5 EBot (.bot CooperateBot) (.sim .opp (.bot DefectBot))
        (.const Action.D)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
        Action.C Action.C
        (by unfold EBot; rfl) hEBotBotCB_outer
      simpa [eval] using hPlay
    have hGuard3 : eval (fuel + 7) OBot EBot (.sim .opp (.bot CooperateBot)) = some .D :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hEBotBotCB
    have hB : play (fuel + 8) OBot EBot = some .D := by
        have hPlay := play_ite_from_guard
            fuel 7 OBot EBot (.sim .opp (.bot CooperateBot))
            (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
            (.const Action.D)
            Action.C Action.D
            (by rfl) hGuard3
        simpa [eval] using hPlay
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

import PrisonersDilemma.Models.DBot

namespace PD.Proofs.DBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.DBot

/-- Pipeline-style action claim for DBot vs CooperateBot. -/
theorem dbot_vs_cooperate_actionClaim :
    ActionClaim Bot.dBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (source Bot.cooperateBot),
    evalSource Bot.cooperateBot (source Bot.dBot)) = (D, C)
  simp [evalSource, source, dBotAction, dBotStrategy, actionFor, evalActionExpr,
    PD.Models.CooperateBot.action, PD.Models.CooperateBot.strategy]

/-- Pipeline-style action claim for DBot vs DefectBot. -/
theorem dbot_vs_defect_actionClaim :
    ActionClaim Bot.dBot Bot.defectBot C D := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (source Bot.defectBot),
    evalSource Bot.defectBot (source Bot.dBot)) = (C, D)
  simp [evalSource, source, dBotAction, dBotStrategy, actionFor, evalActionExpr,
    PD.Models.DefectBot.action, PD.Models.DefectBot.strategy]

/-- Pipeline-style action claim for DBot vs DBot. -/
theorem dbot_vs_dbot_actionClaim :
    ActionClaim Bot.dBot Bot.dBot C C := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (source Bot.dBot),
    evalSource Bot.dBot (source Bot.dBot)) = (C, C)
  simp [evalSource, source, dBotAction, dBotStrategy, actionFor, evalActionExpr]

end PD.Proofs.DBot

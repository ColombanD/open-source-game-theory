import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Models.Bots.DBot

namespace PD.Proofs.DBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.BotUniverse
open PD.Models.Bots.DBot
open PD.Models.Bots

/-- Pipeline-style action claim for DBot vs CooperateBot. -/
theorem dbot_vs_cooperate_actionClaim :
    ActionClaim Bot.dBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.dBot)) = (D, C)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr,
    CooperateBot.action, CooperateBot.strategy]

/-- Pipeline-style action claim for DBot vs DefectBot. -/
theorem dbot_vs_defect_actionClaim :
    ActionClaim Bot.dBot Bot.defectBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.dBot)) = (C, D)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr,
    DefectBot.action, DefectBot.strategy]

/-- Pipeline-style action claim for DBot vs DBot. -/
theorem dbot_vs_dbot_actionClaim :
    ActionClaim Bot.dBot Bot.dBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.dBot)) = (C, C)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr]

end PD.Proofs.DBot

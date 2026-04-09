import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Models.Bots.TitForTatBot

namespace PD.Proofs.TitForTatBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.BotUniverse
open PD.Models.Bots.TitForTatBot
open PD.Models.Bots

/-- Pipeline-style action claim for TitForTatBot vs CooperateBot. -/
theorem titForTatBot_vs_cooperate_actionClaim :
    ActionClaim Bot.titForTatBot Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.titForTatBot)) = (C, C)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr,
    CooperateBot.action, CooperateBot.strategy]

/-- Pipeline-style action claim for TitForTatBot vs DefectBot. -/
theorem titForTatBot_vs_defect_actionClaim :
    ActionClaim Bot.titForTatBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.titForTatBot)) = (D, D)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr,
    DefectBot.action, DefectBot.strategy]

/-- Pipeline-style action claim for TitForTatBot vs TitForTatBot. -/
theorem titForTatBot_vs_titForTatBot_actionClaim :
    ActionClaim Bot.titForTatBot Bot.titForTatBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.titForTatBot)) = (C, C)
  simp [botEvalSource, botSource, action, strategy, actionFor, evalActionExpr]

/-- Pipeline-style action claim for TitForTatBot vs DBot. -/

end PD.Proofs.TitForTatBot

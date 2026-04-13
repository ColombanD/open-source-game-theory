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
  unfold botEvalSource
  simp
  unfold getBotData
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for DBot vs DefectBot. -/
theorem dbot_vs_defect_actionClaim :
    ActionClaim Bot.dBot Bot.defectBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.dBot)) = (C, D)
  unfold botEvalSource
  simp
  unfold getBotData
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for DBot vs DBot. -/
theorem dbot_vs_dbot_actionClaim :
    ActionClaim Bot.dBot Bot.dBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.dBot)) = (D, D)
  unfold botEvalSource
  simp
  unfold getBotData
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for DBot vs TitForTatBot. -/
theorem dbot_vs_titForTatBot_actionClaim :
    ActionClaim Bot.dBot Bot.titForTatBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.dBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.dBot)) = (C, D)
  unfold botEvalSource
  simp
  unfold getBotData
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

end PD.Proofs.DBot

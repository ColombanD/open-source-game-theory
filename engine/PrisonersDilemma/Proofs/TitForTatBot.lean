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
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for TitForTatBot vs DefectBot. -/
theorem titForTatBot_vs_defect_actionClaim :
    ActionClaim Bot.titForTatBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.titForTatBot)) = (D, D)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for TitForTatBot vs TitForTatBot. -/
theorem titForTatBot_vs_titForTatBot_actionClaim :
    ActionClaim Bot.titForTatBot Bot.titForTatBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.titForTatBot)) = (C, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for TitForTatBot vs DBot. -/
theorem titForTatBot_vs_dbot_actionClaim :
    ActionClaim Bot.titForTatBot Bot.dBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.titForTatBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.titForTatBot)) = (D, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

end PD.Proofs.TitForTatBot

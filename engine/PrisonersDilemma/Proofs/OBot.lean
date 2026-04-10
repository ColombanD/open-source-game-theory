import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Models.Bots.OBot

namespace PD.Proofs.OBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.BotUniverse
open PD.Models.Bots.OBot
open PD.Models.Bots

/-- Pipeline-style action claim for OBot vs CooperateBot. -/
theorem oBot_vs_cooperate_actionClaim :
  ActionClaim Bot.oBot Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.oBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.oBot)) = (C, C)
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

/-- Pipeline-style action claim for OBot vs DefectBot. -/
theorem oBot_vs_defect_actionClaim :
  ActionClaim Bot.oBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.oBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.oBot)) = (D, D)
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
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for OBot vs DBot. -/
theorem oBot_vs_dBot_actionClaim :
  ActionClaim Bot.oBot Bot.dBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.oBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.oBot)) = (D, C)
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
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for OBot vs TitForTatBot. -/
theorem oBot_vs_titForTat_actionClaim :
  ActionClaim Bot.oBot Bot.titForTatBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.oBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.oBot)) = (D, C)
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
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for OBot vs OBot. -/
theorem oBot_vs_oBot_actionClaim :
  ActionClaim Bot.oBot Bot.oBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.oBot (botSource Bot.oBot),
    botEvalSource Bot.oBot (botSource Bot.oBot)) = (D, D)
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
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

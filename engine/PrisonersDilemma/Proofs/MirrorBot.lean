import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Models.Bots.MirrorBot

namespace PD.Proofs.MirrorBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.BotUniverse
open PD.Models.Bots.MirrorBot
open PD.Models.Bots

/-- Pipeline-style action claim for MirrorBot vs CooperateBot. -/
theorem mirrorBot_vs_cooperate_actionClaim :
    ActionClaim Bot.mirrorBot Bot.cooperateBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.mirrorBot)) = (C, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for MirrorBot vs DefectBot. -/
theorem mirrorBot_vs_defect_actionClaim :
    ActionClaim Bot.mirrorBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.mirrorBot)) = (D, D)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for MirrorBot vs DBot. -/
theorem mirrorBot_vs_dBot_actionClaim :
    ActionClaim Bot.mirrorBot Bot.dBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.mirrorBot)) = (C, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for MirrorBot vs TitForTatBot. -/
theorem mirrorBot_vs_titForTatBot_actionClaim :
    ActionClaim Bot.mirrorBot Bot.titForTatBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.mirrorBot)) = (C, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for MirrorBot vs OBot. -/
theorem mirrorBot_vs_oBot_actionClaim :
    ActionClaim Bot.mirrorBot Bot.oBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.oBot),
    botEvalSource Bot.oBot (botSource Bot.mirrorBot)) = (C, D)
  unfold botEvalSource
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

/-- Pipeline-style action claim for MirrorBot vs MirrorBot. -/
theorem mirrorBot_vs_mirrorBot_actionClaim :
    ActionClaim Bot.mirrorBot Bot.mirrorBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.mirrorBot (botSource Bot.mirrorBot),
    botEvalSource Bot.mirrorBot (botSource Bot.mirrorBot)) = (C, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

end PD.Proofs.MirrorBot

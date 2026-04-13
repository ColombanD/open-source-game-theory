import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Models.Bots.EBot

namespace PD.Proofs.EBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.BotUniverse
open PD.Models.Bots.EBot
open PD.Models.Bots

/-- Pipeline-style action claim for EBot vs CooperateBot. -/
theorem eBot_vs_cooperate_actionClaim :
    ActionClaim Bot.eBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.cooperateBot),
    botEvalSource Bot.cooperateBot (botSource Bot.eBot)) = (D, C)
  unfold botEvalSource
  simp
  unfold evalActionExpr' evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for EBot vs DefectBot. -/
theorem eBot_vs_defect_actionClaim :
    ActionClaim Bot.eBot Bot.defectBot D D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.defectBot),
    botEvalSource Bot.defectBot (botSource Bot.eBot)) = (D, D)
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

/-- Pipeline-style action claim for EBot vs DBot. -/
theorem eBot_vs_dBot_actionClaim :
    ActionClaim Bot.eBot Bot.dBot D C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.dBot),
    botEvalSource Bot.dBot (botSource Bot.eBot)) = (D, C)
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

/-- Pipeline-style action claim for EBot vs TitForTatBot. -/
theorem eBot_vs_titForTatBot_actionClaim :
    ActionClaim Bot.eBot Bot.titForTatBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.titForTatBot),
    botEvalSource Bot.titForTatBot (botSource Bot.eBot)) = (C, D)
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

/-- Pipeline-style action claim for EBot vs OBot. -/
theorem eBot_vs_oBot_actionClaim :
    ActionClaim Bot.eBot Bot.oBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.oBot),
    botEvalSource Bot.oBot (botSource Bot.eBot)) = (C, D)
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
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for EBot vs EBot. -/
theorem eBot_vs_eBot_actionClaim :
    ActionClaim Bot.eBot Bot.eBot C C := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.eBot),
    botEvalSource Bot.eBot (botSource Bot.eBot)) = (C, C)
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
  unfold probeOpponent evalActionExpr
  simp
  unfold probeOpponent evalActionExpr
  simp

/-- Pipeline-style action claim for EBot vs MirrorBot. -/
theorem eBot_vs_mirrorBot_actionClaim :
    ActionClaim Bot.eBot Bot.mirrorBot C D := by
  unfold ActionClaim playActions
  change (botEvalSource Bot.eBot (botSource Bot.mirrorBot),
    botEvalSource Bot.mirrorBot (botSource Bot.eBot)) = (C, D)
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
  unfold probeOpponent evalActionExpr
  simp

end PD.Proofs.EBot

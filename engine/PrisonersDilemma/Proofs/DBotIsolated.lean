import PrisonersDilemma.Models.DBotIsolated

namespace PD.Proofs.DBotIsolated

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.DBotIsolated

/-- Pipeline-style action claim for DBot vs CooperateBot. -/
theorem dbot_vs_cooperate_actionClaim :
    ActionClaim Bot.dBot Bot.cooperateBot D C := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (PD.Models.DBotIsolated.source Bot.cooperateBot),
    evalSource Bot.cooperateBot (PD.Models.DBotIsolated.source Bot.dBot)) = (D, C)
  simp [evalSource, PD.Models.DBotIsolated.source, dBotAction, dBotStrategy, actionFor, evalActionExpr,
    PD.Models.CooperateBot.action, PD.Models.CooperateBot.strategy]

/-- Pipeline-style action claim for DBot vs DefectBot. -/
theorem dbot_vs_defect_actionClaim :
    ActionClaim Bot.dBot Bot.defectBot C D := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (PD.Models.DBotIsolated.source Bot.defectBot),
    evalSource Bot.defectBot (PD.Models.DBotIsolated.source Bot.dBot)) = (C, D)
  simp [evalSource, PD.Models.DBotIsolated.source, dBotAction, dBotStrategy, actionFor, evalActionExpr,
    PD.Models.DefectBot.action, PD.Models.DefectBot.strategy]

/-- Pipeline-style action claim for DBot vs DBot. -/
theorem dbot_vs_dbot_actionClaim :
    ActionClaim Bot.dBot Bot.dBot C C := by
  unfold ActionClaim playActions
  change (evalSource Bot.dBot (PD.Models.DBotIsolated.source Bot.dBot),
    evalSource Bot.dBot (PD.Models.DBotIsolated.source Bot.dBot)) = (C, C)
  simp [evalSource, PD.Models.DBotIsolated.source, dBotAction, dBotStrategy, actionFor, evalActionExpr]

end PD.Proofs.DBotIsolated

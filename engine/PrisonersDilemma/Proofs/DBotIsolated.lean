import PrisonersDilemma.Models.DBotIsolated

namespace PD.Proofs.DBotIsolated

open PD
open PD.Action
open PD.Models.StrategyDSL
open PD.Models.DBotIsolated

/-- Against an always-cooperating opponent, DBot defects while the opponent cooperates. -/
theorem dbot_vs_cooperate_actions :
    (dBotAction cooperateSource, C) = (D, C) := by
  simp [dBotAction, dBotStrategy, actionFor, evalActionExpr]

/-- Against an always-defecting opponent, DBot cooperates while the opponent defects. -/
theorem dbot_vs_defect_actions :
    (dBotAction defectSource, D) = (C, D) := by
  simp [dBotAction, dBotStrategy, actionFor, evalActionExpr]

/-- Against itself in this isolated model, DBot cooperates on both sides. -/
theorem dbot_vs_dbot_actions :
    (dBotAction dBotSource, dBotAction dBotSource) = (C, C) := by
  simp [dBotAction, dBotStrategy, dBotSource, actionFor, evalActionExpr]

end PD.Proofs.DBotIsolated

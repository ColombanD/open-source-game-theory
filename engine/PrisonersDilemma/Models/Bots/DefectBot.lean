import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.DefectBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for DefectBot. -/
@[simp]
def strategy (oppSource : SourceAST) : ActionExpr :=
  ActionExpr.actionLit D

/-- Source encoding for DefectBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := strategy }

/-- Action chosen by DefectBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr (strategy oppSource) oppSource.tag

end PD.Models.Bots.DefectBot

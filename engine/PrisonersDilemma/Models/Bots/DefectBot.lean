import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.DefectBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy expression for DefectBot. -/
@[simp]
def strategyExpr : ActionExpr :=
  ActionExpr.actionLit D

/-- Strategy definition for DefectBot. -/
@[simp]
def strategy (_oppSource : SourceAST) : ActionExpr :=
  strategyExpr

/-- Source encoding for DefectBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := strategyExpr }

/-- Action chosen by DefectBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr (strategy oppSource) oppSource.tag

end PD.Models.Bots.DefectBot

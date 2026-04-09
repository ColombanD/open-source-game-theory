import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.CooperateBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy expression for CooperateBot. -/
@[simp]
def strategyExpr : ActionExpr :=
  ActionExpr.actionLit C

/-- Strategy definition for CooperateBot. -/
@[simp]
def strategy (_oppSource : SourceAST) : ActionExpr :=
  strategyExpr

/-- Source encoding for CooperateBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := strategyExpr }

/-- Action chosen by CooperateBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr (strategy oppSource) oppSource.tag

end PD.Models.Bots.CooperateBot

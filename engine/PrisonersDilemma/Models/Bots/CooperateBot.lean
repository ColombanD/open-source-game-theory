import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.CooperateBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for CooperateBot. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.actionLit C

/-- Source encoding for CooperateBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := strategy }

/-- Action chosen by CooperateBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.CooperateBot

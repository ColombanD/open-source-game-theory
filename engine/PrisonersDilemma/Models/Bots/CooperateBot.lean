import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.CooperateBot

open PD
open PD.Action
open PD.StrategyDSL

@[simp] def strategy : ActionExpr := ActionExpr.actionLit C

@[simp] def source : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := strategy }

@[simp] def action (oppSource : SourceAST) : Action :=
  actionFor strategy oppSource

end PD.Models.Bots.CooperateBot

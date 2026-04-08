import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.DefectBot

open PD
open PD.Action
open PD.StrategyDSL

@[simp] def strategy : ActionExpr := ActionExpr.actionLit D

@[simp] def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := strategy }

@[simp] def action (oppSource : SourceAST) : Action :=
  actionFor strategy oppSource

end PD.Models.Bots.DefectBot

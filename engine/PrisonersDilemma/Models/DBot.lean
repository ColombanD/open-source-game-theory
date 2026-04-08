import PrisonersDilemma.StrategyDSL

namespace PD.Models.DBot

open PD
open PD.Action
open PD.StrategyDSL
/-- DBot-specific strategy definition.
    This is the only strategy this file is responsible for. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.ifOppIs SourceTag.cooperateTag
    (ActionExpr.actionLit D) -- If yes
    (ActionExpr.actionLit C) -- If no

/-- Optional source value carrying DBot strategy. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := strategy }

/-- DBot action as a function of opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  actionFor strategy oppSource

end PD.Models.DBot

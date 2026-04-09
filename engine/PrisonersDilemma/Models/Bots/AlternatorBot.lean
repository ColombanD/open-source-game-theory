import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.AlternatorBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Condition used by Alternator strategy in one-shot open-source PD. -/
@[simp]
def condition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.oppIs SourceTag.titForTatTag)

/-- Strategy definition for AlternatorBot. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.ifThenElse condition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

/-- Source encoding for AlternatorBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.alternatorTag, strategy := strategy }

/-- Action chosen by AlternatorBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.AlternatorBot

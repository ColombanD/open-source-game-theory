import PrisonersDilemma.Models.OpenSourceStrategyDSL

namespace PD.Models.Bots.AlternatorBot

open PD
open PD.Action
open PD.Models.OpenSourceStrategyDSL

/-- Alternator condition in one-shot open-source PD:
cooperate against CooperateBot and TitForTat, defect otherwise. -/
@[simp]
def condition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.oppIs SourceTag.titForTatTag)

@[simp]
def strategy : ActionExpr :=
  ActionExpr.ifThenElse condition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

@[simp]
def source : SourceAST :=
  { tag := SourceTag.alternatorTag, strategy := strategy }

@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.AlternatorBot

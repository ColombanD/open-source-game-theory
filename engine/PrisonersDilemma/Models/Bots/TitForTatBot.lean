import PrisonersDilemma.Models.OpenSourceStrategyDSL

namespace PD.Models.Bots.TitForTatBot

open PD
open PD.Action
open PD.Models.OpenSourceStrategyDSL

/-- TitForTat condition in one-shot open-source PD:
cooperate against cooperative-looking opponents, defect otherwise. -/
@[simp]
def condition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.or (BoolExpr.oppIs SourceTag.titForTatTag)
      (BoolExpr.oppIs SourceTag.alternatorTag))

@[simp]
def strategy : ActionExpr :=
  ActionExpr.ifThenElse condition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

@[simp]
def source : SourceAST :=
  { tag := SourceTag.titForTatTag, strategy := strategy }

@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.TitForTatBot

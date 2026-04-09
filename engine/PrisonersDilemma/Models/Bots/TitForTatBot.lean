import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.TitForTatBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Condition used by TitForTat strategy in one-shot open-source PD. -/
@[simp]
def condition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.or (BoolExpr.oppIs SourceTag.titForTatTag)
      (BoolExpr.oppIs SourceTag.alternatorTag))

/-- Strategy definition for TitForTatBot. -/
@[simp]
def strategy: ActionExpr :=
  ActionExpr.ifThenElse condition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

/-- Source encoding for TitForTatBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.titForTatTag, strategy := strategy }

/-- Action chosen by TitForTatBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.TitForTatBot

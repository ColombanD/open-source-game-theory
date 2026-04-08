import PrisonersDilemma.Pipeline

namespace PD.Models.OpenSourceStrategyDSL

open PD
open PD.Action

/-- Bot labels available to source-level predicates about opponents. -/
inductive SourceTag : Type where
  | cooperateTag : SourceTag
  | defectTag : SourceTag
  | dBotTag : SourceTag
  | titForTatTag : SourceTag
  | suspiciousTFTTag : SourceTag
  | alternatorTag : SourceTag
  deriving DecidableEq, Repr

/-- Boolean expressions over opponent source tags. -/
inductive BoolExpr : Type where
  | oppIs : SourceTag -> BoolExpr
  | not : BoolExpr -> BoolExpr
  | and : BoolExpr -> BoolExpr -> BoolExpr
  | or : BoolExpr -> BoolExpr -> BoolExpr
  deriving DecidableEq, Repr

/-- Action programs built from literals and branching on source predicates. -/
inductive ActionExpr : Type where
  | actionLit : Action -> ActionExpr
  | ifThenElse : BoolExpr -> ActionExpr -> ActionExpr -> ActionExpr
  deriving DecidableEq, Repr

/-- Full source representation: a declared bot tag and its strategy AST. -/
structure SourceAST : Type where
  tag : SourceTag
  strategy : ActionExpr
  deriving DecidableEq, Repr

@[simp] def cooperateStrategy : ActionExpr := ActionExpr.actionLit C
@[simp] def defectStrategy : ActionExpr := ActionExpr.actionLit D

/-- Evaluate a source predicate against opponent tag metadata. -/
@[simp]
def evalBoolExpr (e : BoolExpr) (oppTag : SourceTag) : Bool :=
  match e with
  | BoolExpr.oppIs tag => oppTag = tag
  | BoolExpr.not e1 => !(evalBoolExpr e1 oppTag)
  | BoolExpr.and e1 e2 => (evalBoolExpr e1 oppTag) && (evalBoolExpr e2 oppTag)
  | BoolExpr.or e1 e2 => (evalBoolExpr e1 oppTag) || (evalBoolExpr e2 oppTag)

/-- Evaluate a source strategy AST given the opponent source metadata. -/
@[simp]
def evalActionExpr (e : ActionExpr) (oppTag : SourceTag) : Action :=
  match e with
  | ActionExpr.actionLit a => a
  | ActionExpr.ifThenElse cond tBranch eBranch =>
      if evalBoolExpr cond oppTag then
        evalActionExpr tBranch oppTag
      else
        evalActionExpr eBranch oppTag

/-- Evaluate an opponent source against a fixed probe input source. -/
@[simp]
def probeOpponent (oppSource probeInput : SourceAST) : Action :=
  evalActionExpr oppSource.strategy probeInput.tag

end PD.Models.OpenSourceStrategyDSL

import PrisonersDilemma.Pipeline

namespace PD.Models.StrategyDSL

open PD
open PD.Action

/-!
Beginner-friendly strategy DSL used by small model files.

Mental model:
1. `SourceTag` is metadata about the opponent source.
2. `ActionExpr` is a tiny strategy language.
3. `evalActionExpr` executes a strategy expression on opponent metadata.
4. `probeOpponent` runs one source against another source.
-/

/-- Minimal source labels used for source-aware branching. -/
inductive SourceTag : Type where
  | cooperateTag : SourceTag
  | defectTag : SourceTag
  deriving DecidableEq, Repr

/-- Tiny strategy language: literal action or source-based branch. -/
inductive ActionExpr : Type where
  | actionLit : Action -> ActionExpr
  | ifOppIs : SourceTag -> ActionExpr -> ActionExpr -> ActionExpr
  deriving DecidableEq, Repr

/-- Source representation: metadata tag + strategy AST. -/
structure SourceAST : Type where
  tag : SourceTag
  strategy : ActionExpr
  deriving DecidableEq, Repr

@[simp] def cooperateStrategy : ActionExpr := ActionExpr.actionLit C
@[simp] def defectStrategy : ActionExpr := ActionExpr.actionLit D

@[simp] def cooperateSource : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := cooperateStrategy }

@[simp] def defectSource : SourceAST :=
  { tag := SourceTag.defectTag, strategy := defectStrategy }

/-- Execute a strategy expression against opponent source metadata. -/
@[simp]
def evalActionExpr (e : ActionExpr) (oppTag : SourceTag) : Action :=
  match e with
  | ActionExpr.actionLit a => a
  | ActionExpr.ifOppIs expected tBranch eBranch =>
      if oppTag = expected then
        evalActionExpr tBranch oppTag
      else
        evalActionExpr eBranch oppTag

/-- Probe helper: evaluate opponent strategy on a chosen probe source.
This is a simple way to test how a strategy behaves against a specific opponent source. -/
@[simp]
def probeOpponent (oppSource probeInput : SourceAST) : Action :=
  evalActionExpr oppSource.strategy probeInput.tag

/-- Uniform helper: run any strategy against an opponent source. -/
@[simp]
def actionFor (strategy : ActionExpr) (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.StrategyDSL

import PrisonersDilemma.Pipeline

namespace PD.StrategyDSL

open PD
open PD.Action

/-- Witness that Action is nonempty, required for partial functions returning Action. -/
instance : Nonempty Action := ⟨C⟩

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
  | dBotTag: SourceTag
  | titForTatTag : SourceTag
  deriving DecidableEq, Repr

mutual
/-- Tiny strategy language: literal action, source-based branch, or probe-based branch. -/
  inductive ActionExpr : Type where
    | actionLit : Action -> ActionExpr
    | ifOppIs : SourceTag -> ActionExpr -> ActionExpr -> ActionExpr
    | probeAndBranch : SourceAST -> Action -> ActionExpr -> ActionExpr -> ActionExpr
    deriving DecidableEq, Repr

  /-- Source representation: metadata tag + strategy AST. -/
  structure SourceAST : Type where
    tag : SourceTag
    strategy : ActionExpr
    deriving DecidableEq, Repr
end

mutual
/-- Mutual recursion between evalActionExpr and probeOpponent.
   These are marked `partial` because termination cannot be guaranteed structurally:
   bots can probe other bots, potentially creating cycles (e.g., Bot A probes Bot B,
   which probes Bot A). Real termination depends on how users structure their bot definitions.
   In practice, well-designed bots avoid such circular probing. -/
  partial def evalActionExpr (e : ActionExpr) (oppSource : SourceAST) : Action :=
    match e with
    | ActionExpr.actionLit a => a
    | ActionExpr.ifOppIs expected tBranch eBranch =>
        if oppSource.tag = expected then
          evalActionExpr tBranch oppSource
        else
          evalActionExpr eBranch oppSource
    | ActionExpr.probeAndBranch probeSource expectedAction tBranch eBranch =>
        -- Probe the opponent with a chosen probe source and branch based on the result.
        -- If opponent's response matches expectedAction, take tBranch; otherwise take eBranch.
        let probeResult := probeOpponent oppSource probeSource
        if probeResult = expectedAction then
          evalActionExpr tBranch oppSource
        else
          evalActionExpr eBranch oppSource

  /-- Probe helper: evaluate opponent strategy against a chosen probe source. -/
  partial def probeOpponent (oppSource probeInput : SourceAST) : Action :=
    evalActionExpr oppSource.strategy probeInput
end

/-- Uniform helper: run any strategy against an opponent source. -/
@[simp]
def actionFor (strategy : ActionExpr) (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource

end PD.StrategyDSL

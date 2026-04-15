import PrisonersDilemma.Pipeline

namespace PD.StrategyDSL

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
  | dBotTag: SourceTag
  | titForTatTag : SourceTag
  | oBotTag : SourceTag
  | mirrorBotTag : SourceTag
  | eBotTag : SourceTag
  | cupodTag : SourceTag
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
   These functions take a fuel parameter to ensure termination,
   even if bots probe other bots. Fuel decreases with each recursive call,
   preventing infinite loops.

   Returns Option Action: some action if evaluation succeeds, none if fuel exhausted. -/
  def evalActionExpr (fuel : Nat) (e : ActionExpr) (oppSource : SourceAST) : Option Action :=
    match fuel with
    | 0 => none  -- Out of fuel
    | fuel + 1 =>
      match e with
      | ActionExpr.actionLit a => some a
      | ActionExpr.ifOppIs expected tBranch eBranch =>
          if oppSource.tag = expected then
            evalActionExpr fuel tBranch oppSource
          else
            evalActionExpr fuel eBranch oppSource
      | ActionExpr.probeAndBranch probeSource expectedAction tBranch eBranch =>
          -- Probe the opponent with a chosen probe source and branch based on the result.
          -- If opponent's response matches expectedAction, take tBranch; otherwise take eBranch.
          let probeResult := probeOpponent fuel oppSource probeSource
          match probeResult with
          | none => none
          | some result =>
              if result = expectedAction then
                evalActionExpr fuel tBranch oppSource
              else
                evalActionExpr fuel eBranch oppSource

  /-- Probe helper: evaluate opponent strategy against a chosen probe source. -/
  def probeOpponent (fuel : Nat) (oppSource probeInput : SourceAST) : Option Action :=
    evalActionExpr fuel oppSource.strategy probeInput
end

/-- Wrapper: evaluate strategy with default fuel of 100. -/
def evalActionExpr' (e : ActionExpr) (oppSource : SourceAST) : Action :=
  match evalActionExpr 100 e oppSource with
  | some a => a
  | none => C  -- Fallback if fuel exhausted

/-- Wrapper: probe opponent with default fuel of 100. -/
def probeOpponent' (oppSource probeInput : SourceAST) : Action :=
  match probeOpponent 100 oppSource probeInput with
  | some a => a
  | none => C  -- Fallback if fuel exhausted

/-- Uniform helper: run any strategy against an opponent source. -/
@[simp]
def actionFor (strategy : ActionExpr) (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.StrategyDSL

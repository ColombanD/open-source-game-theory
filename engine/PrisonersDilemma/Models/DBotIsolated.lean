import PrisonersDilemma.Pipeline

namespace PD.Models.DBotIsolated

/-!
`DBotIsolated.lean` is a minimal teaching file for the Contrarian Probe bot.

How to read this file:
1. Define tiny data types for "source code" and "strategies".
2. Define an evaluator for that tiny strategy language.
3. Define probing (`probeOpponent`) and then DBot's rule (`dBotAction`).
4. Check behavior with simple `example` proofs.

This mirrors the larger `OpenSourceBots.lean` model but keeps only what DBot needs.
-/

open PD
open PD.Action

/-- Minimal source tags used in this isolated dBot model. -/
inductive SourceTag : Type where
  -- Q: What is the role of `SourceTag`?
  -- A: It is compact source-level metadata. Instead of parsing full source code,
  -- we attach a small label (e.g., cooperateTag / defectTag) to each bot source.
  -- Strategies and probes can then branch on this label, which keeps the model
  -- simple while still representing "code-aware" behavior.
  -- Opponent looks like an always-cooperate bot.
  | cooperateTag : SourceTag
  -- Opponent looks like an always-defect bot.
  | defectTag : SourceTag
  deriving DecidableEq, Repr

/-- Tiny strategy language for this tutorial file. -/
inductive ActionExpr : Type where
  -- Q: Why does `ActionExpr` have a richer structure than `SourceTag` even though both are inductive?
  -- A: Because they model different kinds of information. `SourceTag` is just a
  -- small label, so its constructors are only names. `ActionExpr` is a program
  -- language, so it needs constructors that can build behavior: a literal action
  -- or a conditional branch. In other words, `SourceTag` classifies sources;
  -- `ActionExpr` describes what a source does.
  -- Return a literal action (C or D).
  | actionLit : Action -> ActionExpr
  -- Conditional: branch on the opponent's source tag.
  | ifOppIs : SourceTag -> ActionExpr -> ActionExpr -> ActionExpr
  deriving DecidableEq, Repr

/-- Source metadata + strategy code. -/
structure SourceAST : Type where
  -- Tag used for simple source-level pattern checks.
  tag : SourceTag
  -- Strategy program in our tiny AST.
  strategy : ActionExpr
  deriving DecidableEq, Repr

-- Lean syntax on this line:
-- `@[simp]` marks the definition as a simplification rule.
-- `def` introduces a named definition.
-- `cooperateStrategy` is the name being defined.
-- `:` says what type the name has.
-- `ActionExpr` is that type.
-- `:=` starts the defining expression.
-- `ActionExpr.actionLit C` is the body of the definition: the value Lean
-- associates with `cooperateStrategy`, and what it unfolds to later.
@[simp] def cooperateStrategy : ActionExpr := ActionExpr.actionLit C
@[simp] def defectStrategy : ActionExpr := ActionExpr.actionLit D

-- Canonical source values used as probe inputs.
@[simp] def cooperateSource : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := cooperateStrategy }

@[simp] def defectSource : SourceAST :=
  { tag := SourceTag.defectTag, strategy := defectStrategy }

/-- Evaluate a strategy expression against an opponent tag. -/
@[simp]
def evalActionExpr (e : ActionExpr) (oppTag : SourceTag) : Action :=
  -- `match e with` case-splits on the constructor used to build `e`.
  -- In Lean syntax, this is how we inspect an inductive value.
  match e with
  -- `ActionExpr.actionLit a` means `e` was built from the `actionLit`
  -- constructor, and the variable `a` stores the action inside it.
  -- Semantics: just return that action directly.
  | ActionExpr.actionLit a => a
  -- `ActionExpr.ifOppIs expected tBranch eBranch` means `e` was built from
  -- the conditional constructor. Lean binds three pieces of data:
  -- `expected` is the tag we are testing against,
  -- `tBranch` is the branch to use when the test succeeds,
  -- `eBranch` is the branch to use when the test fails.
  -- The `=>` introduces the right-hand side for this pattern.
  | ActionExpr.ifOppIs expected tBranch eBranch =>
      -- `if ... then ... else ...` is the ordinary Lean conditional.
      -- Here the condition is whether the opponent's tag matches the one
      -- stored in the constructor.
      if oppTag = expected then
        -- Semantics: if the tag matches, evaluate the "then" branch.
        -- We recursively call `evalActionExpr` because branches are themselves
        -- `ActionExpr` values.
        evalActionExpr tBranch oppTag
      else
        -- Semantics: if the tag does not match, evaluate the "else" branch.
        -- The same opponent tag is passed through because it is still the
        -- input we are evaluating against.
        evalActionExpr eBranch oppTag

/-- Probe helper: run opponent strategy on a chosen probe input source. -/
@[simp]
def probeOpponent (oppSource probeInput : SourceAST) : Action :=
  -- Lean syntax here:
  -- `(oppSource probeInput : SourceAST)` means there are two parameter names,
  -- `oppSource` and `probeInput`, and both have the same type `SourceAST`.
  -- This is shorthand for writing two separate typed arguments.
  -- `: Action` says that the function returns an `Action`.
  -- "Ask": what does opponent do if faced with `probeInput`?
  evalActionExpr oppSource.strategy probeInput.tag

/-- Isolated DBot rule:
    If opponent cooperates with DefectBot, then defect; else cooperate. -/
@[simp]
def dBotAction (oppSource : SourceAST) : Action :=
  -- This is the core contrarian probe behavior.
  if probeOpponent oppSource defectSource = C then D else C

end PD.Models.DBotIsolated

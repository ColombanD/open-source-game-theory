import PrisonersDilemma.Pipeline -- Import core PD abstractions (actions, payoffs, and simulation pipeline).

namespace PD.Models.OpenSourceBots -- Namespace for a richer hand-coded bot population.

open PD -- Bring shared PD names into scope (`ProgramModel`, `Action`, payoff helpers, ...).
open PD.Action -- Allow writing `C`/`D` directly instead of `Action.C`/`Action.D`.

/-- Bot strategies in the open-source one-shot prisoner's dilemma. -/
inductive Bot : Type where -- Finite strategy set used for deterministic one-shot evaluation.
  | cooperateBot : Bot -- Always cooperates.
  | defectBot : Bot -- Always defects.
  | titForTat : Bot -- Cooperates with cooperative-looking bots, defects otherwise.
  | suspiciousTFT : Bot -- Always defects in this one-shot encoding.
  | alternator : Bot -- Encoded alternator behavior via opponent-dependent one-shot cases.
  deriving DecidableEq, Repr -- Derive equality checks and printable representation.

/-- Bot labels available to source-level predicates about opponents. -/
inductive SourceTag : Type where
  | cooperateTag : SourceTag
  | defectTag : SourceTag
  | titForTatTag : SourceTag
  | suspiciousTFTTag : SourceTag
  | alternatorTag : SourceTag
  deriving DecidableEq, Repr

/-- Boolean expressions over opponent source tags. -/
inductive BoolExpr : Type where
  | oppIs : SourceTag → BoolExpr
  | not : BoolExpr → BoolExpr
  | and : BoolExpr → BoolExpr → BoolExpr
  | or : BoolExpr → BoolExpr → BoolExpr
  deriving DecidableEq, Repr

/-- Action programs built from literals and branching on source predicates. -/
inductive ActionExpr : Type where
  | actionLit : Action → ActionExpr
  | ifThenElse : BoolExpr → ActionExpr → ActionExpr → ActionExpr
  deriving DecidableEq, Repr

/-- Full source representation: a declared bot tag and its strategy AST. -/
structure SourceAST : Type where
  tag : SourceTag
  strategy : ActionExpr
  deriving DecidableEq, Repr

@[simp] def cooperateStrategy : ActionExpr := ActionExpr.actionLit C
@[simp] def defectStrategy : ActionExpr := ActionExpr.actionLit D

@[simp]
def titForTatCondition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.or (BoolExpr.oppIs SourceTag.titForTatTag)
      (BoolExpr.oppIs SourceTag.alternatorTag))

@[simp]
def alternatorCondition : BoolExpr :=
  BoolExpr.or (BoolExpr.oppIs SourceTag.cooperateTag)
    (BoolExpr.oppIs SourceTag.titForTatTag)

@[simp]
def titForTatStrategy : ActionExpr :=
  ActionExpr.ifThenElse titForTatCondition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

@[simp]
def alternatorStrategy : ActionExpr :=
  ActionExpr.ifThenElse alternatorCondition (ActionExpr.actionLit C) (ActionExpr.actionLit D)

/-- Source-code encoding for each bot as a strategy AST. -/
@[simp] def cooperateBotSource : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := cooperateStrategy }

@[simp] def defectBotSource : SourceAST :=
  { tag := SourceTag.defectTag, strategy := defectStrategy }

@[simp] def titForTatSource : SourceAST :=
  { tag := SourceTag.titForTatTag, strategy := titForTatStrategy }

@[simp] def suspiciousTFTSource : SourceAST :=
  { tag := SourceTag.suspiciousTFTTag, strategy := defectStrategy }

@[simp] def alternatorSource : SourceAST :=
  { tag := SourceTag.alternatorTag, strategy := alternatorStrategy }

@[simp]
def source : Bot → SourceAST
  | Bot.cooperateBot => cooperateBotSource
  | Bot.defectBot => defectBotSource
  | Bot.titForTat => titForTatSource
  | Bot.suspiciousTFT => suspiciousTFTSource
  | Bot.alternator => alternatorSource

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

/-- Source-level evaluator: my action given only opponent source AST. -/
@[simp]
def evalSource (me : Bot) (oppSource : SourceAST) : Action :=
  evalActionExpr (source me).strategy oppSource.tag

instance : ProgramModel Bot where -- Define each bot's action as a function of opponent identity.
  SourceType := SourceAST
  source := source
  actionFromSource := evalSource

/-- Action chosen by a bot against an opponent bot. -/
def eval (me opp : Bot) : Action := -- Convenience wrapper around typeclass-dispatched action selection.
  ProgramModel.action me opp -- Compute `me`'s action against `opp`.

/-- Payoff for the row bot under the canonical PD payoff matrix. -/
def botPayoff (me opp : Bot) : Nat := -- Row player's canonical payoff for a two-bot matchup.
  payoff canonicalPayoff (eval me opp) (eval opp me) -- Use row/column action ordering expected by `payoff`.

/-- Social welfare is the sum of both bots' payoffs. -/
def socialWelfare (me opp : Bot) : Nat := -- Total welfare of the matchup.
  botPayoff me opp + botPayoff opp me -- Add both players' payoffs symmetrically.

end PD.Models.OpenSourceBots -- End namespace for this bot model.

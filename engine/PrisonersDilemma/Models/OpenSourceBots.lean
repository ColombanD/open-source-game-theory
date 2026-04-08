import PrisonersDilemma.Pipeline -- Import core PD abstractions (actions, payoffs, and simulation pipeline).
import PrisonersDilemma.Models.OpenSourceStrategyDSL

namespace PD.Models.OpenSourceBots -- Namespace for a richer hand-coded bot population.

open PD -- Bring shared PD names into scope (`ProgramModel`, `Action`, payoff helpers, ...).
open PD.Action -- Allow writing `C`/`D` directly instead of `Action.C`/`Action.D`.
open PD.Models.OpenSourceStrategyDSL

/-- Bot strategies in the open-source one-shot prisoner's dilemma. -/
inductive Bot : Type where -- Finite strategy set used for deterministic one-shot evaluation.
  | cooperateBot : Bot -- Always cooperates.
  | defectBot : Bot -- Always defects.
  | dBot : Bot -- Contrarian probe: inverts opponent's response to DefectBot.
  | titForTat : Bot -- Cooperates with cooperative-looking bots, defects otherwise.
  | suspiciousTFT : Bot -- Always defects in this one-shot encoding.
  | alternator : Bot -- Encoded alternator behavior via opponent-dependent one-shot cases.
  deriving DecidableEq, Repr -- Derive equality checks and printable representation.

/-- Compatibility aliases to keep existing names available in this module. -/
abbrev SourceTag := OpenSourceStrategyDSL.SourceTag
abbrev BoolExpr := OpenSourceStrategyDSL.BoolExpr
abbrev ActionExpr := OpenSourceStrategyDSL.ActionExpr
abbrev SourceAST := OpenSourceStrategyDSL.SourceAST

@[simp] abbrev cooperateStrategy : ActionExpr := OpenSourceStrategyDSL.cooperateStrategy
@[simp] abbrev defectStrategy : ActionExpr := OpenSourceStrategyDSL.defectStrategy

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

@[simp] def dBotStrategy : ActionExpr := ActionExpr.actionLit C

/-- Source-code encoding for each bot as a strategy AST. -/
@[simp] def cooperateBotSource : SourceAST :=
  { tag := SourceTag.cooperateTag, strategy := cooperateStrategy }

@[simp] def defectBotSource : SourceAST :=
  { tag := SourceTag.defectTag, strategy := defectStrategy }

@[simp] def dBotSource : SourceAST :=
  { tag := SourceTag.dBotTag, strategy := dBotStrategy }

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
  | Bot.dBot => dBotSource
  | Bot.titForTat => titForTatSource
  | Bot.suspiciousTFT => suspiciousTFTSource
  | Bot.alternator => alternatorSource

/-- Resolve a named probe to the corresponding source AST. -/
@[simp] def dBotProbeSource : SourceAST := defectBotSource

@[simp] abbrev evalBoolExpr := OpenSourceStrategyDSL.evalBoolExpr
@[simp] abbrev evalActionExpr := OpenSourceStrategyDSL.evalActionExpr
@[simp] abbrev probeOpponent := OpenSourceStrategyDSL.probeOpponent

/-- DBot: defect if opponent cooperates with DefectBot, else cooperate. -/
@[simp]
def dBotContrarianAction (oppSource : SourceAST) : Action :=
  if probeOpponent oppSource dBotProbeSource = C then D else C

/-- Source-level evaluator: my action given only opponent source AST. -/
@[simp]
def evalSource (me : Bot) (oppSource : SourceAST) : Action :=
  match me with
  | Bot.dBot => dBotContrarianAction oppSource
  | _ => evalActionExpr (source me).strategy oppSource.tag

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

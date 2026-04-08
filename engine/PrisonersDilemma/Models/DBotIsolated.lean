import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.CooperateBot
import PrisonersDilemma.Models.DefectBot

namespace PD.Models.DBotIsolated

/-!
`DBotIsolated.lean` is a minimal teaching file for the Contrarian Probe bot.

How to read this file:
1. Define tiny data types for "source code" and "strategies".
2. Define an evaluator for that tiny strategy language.
3. Define probing (`probeOpponent`) and then DBot's rule (`dBotAction`).

This mirrors the larger `OpenSourceBots.lean` model but keeps only what DBot needs.
-/

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.CooperateBot
open PD.Models.DefectBot

/-- DBot-specific strategy definition.
    This is the only strategy this file is responsible for. -/
@[simp]
def dBotStrategy : ActionExpr :=
  ActionExpr.ifOppIs SourceTag.cooperateTag
    (ActionExpr.actionLit D) -- If yes
    (ActionExpr.actionLit C) -- If no

/-- Optional source value carrying DBot strategy. -/
@[simp]
def dBotSource : SourceAST :=
  { tag := SourceTag.defectTag, strategy := dBotStrategy }

/-- DBot action as a function of opponent source metadata. -/
@[simp]
def dBotAction (oppSource : SourceAST) : Action :=
  actionFor dBotStrategy oppSource

/-- Small bot set used for the isolated, pipeline-native DBot tutorial model. -/
inductive Bot : Type where
  | cooperateBot : Bot
  | defectBot : Bot
  | dBot : Bot
  deriving DecidableEq, Repr

/-- Source encoding used by `ProgramModel` for this tutorial model. -/
@[simp]
def source : Bot -> SourceAST
  | Bot.cooperateBot => CooperateBot.source
  | Bot.defectBot => DefectBot.source
  | Bot.dBot => dBotSource

/-- Source interpreter used by `ProgramModel` for this tutorial model. -/
@[simp]
def evalSource (me : Bot) (oppSource : SourceAST) : Action :=
  match me with
  | Bot.cooperateBot => CooperateBot.action oppSource
  | Bot.defectBot => DefectBot.action oppSource
  | Bot.dBot => dBotAction oppSource

instance : ProgramModel Bot where
  SourceType := SourceAST
  source := source
  actionFromSource := evalSource

/-- Convenience wrapper around pipeline-dispatched action computation. -/
def eval (me opp : Bot) : Action :=
  ProgramModel.action me opp

end PD.Models.DBotIsolated

import PrisonersDilemma.Models.StrategyDSL

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
open PD.Models.StrategyDSL

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

end PD.Models.DBotIsolated

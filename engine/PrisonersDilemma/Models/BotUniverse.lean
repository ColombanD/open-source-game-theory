import PrisonersDilemma.Models.CooperateBot
import PrisonersDilemma.Models.DefectBot
import PrisonersDilemma.Models.DBot

namespace PD.Models.BotUniverse

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.CooperateBot
open PD.Models.DefectBot
open PD.Models.DBot

/-- Shared bot universe for the pipeline-native matchup model. -/
inductive Bot : Type where
  | cooperateBot : Bot
  | defectBot : Bot
  | dBot : Bot
  deriving DecidableEq, Repr

/-- Source encoding used by `ProgramModel` for this shared universe. -/
@[simp]
def botSource : Bot -> SourceAST
  | Bot.cooperateBot => CooperateBot.source
  | Bot.defectBot => DefectBot.source
  | Bot.dBot => DBot.source

/-- Source interpreter used by `ProgramModel` for this shared universe. -/
@[simp]
def botEvalSource (me : Bot) (oppSource : SourceAST) : Action :=
  match me with
  | Bot.cooperateBot => CooperateBot.action oppSource
  | Bot.defectBot => DefectBot.action oppSource
  | Bot.dBot => DBot.action oppSource

instance : ProgramModel Bot where
  SourceType := SourceAST
  source := botSource
  actionFromSource := botEvalSource

/-- Convenience wrapper around pipeline-dispatched action computation. -/
def botEval (me opp : Bot) : Action :=
  ProgramModel.action me opp

end PD.Models.BotUniverse

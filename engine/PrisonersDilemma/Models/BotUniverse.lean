import PrisonersDilemma.Models.Bots.CooperateBot
import PrisonersDilemma.Models.Bots.DefectBot
import PrisonersDilemma.Models.Bots.DBot
import PrisonersDilemma.Models.Bots.TitForTatBot

namespace PD.Models.BotUniverse

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots.CooperateBot
open PD.Models.Bots.TitForTatBot
open PD.Models.Bots.DefectBot
open PD.Models.Bots.DBot

/-- Shared bot universe for the pipeline-native matchup model. -/
inductive Bot : Type where
  | cooperateBot : Bot
  | defectBot : Bot
  | dBot : Bot
  | titForTatBot : Bot
  deriving DecidableEq, Repr

/-- Source encoding used by `ProgramModel` for this shared universe. -/
@[simp]
def botSource : Bot -> SourceAST
  | Bot.cooperateBot => PD.Models.Bots.CooperateBot.source
  | Bot.defectBot => PD.Models.Bots.DefectBot.source
  | Bot.dBot => PD.Models.Bots.DBot.source
  | Bot.titForTatBot => PD.Models.Bots.TitForTatBot.source

/-- Source interpreter used by `ProgramModel` for this shared universe. -/
@[simp]
def botEvalSource (me : Bot) (oppSource : SourceAST) : Action :=
  match me with
  | Bot.cooperateBot => PD.Models.Bots.CooperateBot.action oppSource
  | Bot.defectBot => PD.Models.Bots.DefectBot.action oppSource
  | Bot.dBot => PD.Models.Bots.DBot.action oppSource
  | Bot.titForTatBot => PD.Models.Bots.TitForTatBot.action oppSource

instance : ProgramModel Bot where
  SourceType := SourceAST
  source := botSource
  actionFromSource := botEvalSource

/-- Convenience wrapper around pipeline-dispatched action computation. -/
def botEval (me opp : Bot) : Action :=
  ProgramModel.action me opp

end PD.Models.BotUniverse

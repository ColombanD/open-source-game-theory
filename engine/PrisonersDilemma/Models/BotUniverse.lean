import PrisonersDilemma.Models.Bots.CooperateBot
import PrisonersDilemma.Models.Bots.DefectBot
import PrisonersDilemma.Models.Bots.DBot
import PrisonersDilemma.Models.Bots.TitForTatBot
import PrisonersDilemma.Models.Bots.OBot
import PrisonersDilemma.Models.Bots.EBot
import PrisonersDilemma.Models.Bots.MirrorBot
import PrisonersDilemma.Models.Bots.CupodBot

namespace PD.Models.BotUniverse

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots.CooperateBot
open PD.Models.Bots.TitForTatBot
open PD.Models.Bots.DefectBot
open PD.Models.Bots.DBot
open PD.Models.Bots.OBot
open PD.Models.Bots.EBot
open PD.Models.Bots.MirrorBot
open PD.Models.Bots.CupodBot


/-- Shared bot universe for the pipeline-native matchup model. -/
inductive Bot : Type where
  | cooperateBot : Bot
  | defectBot : Bot
  | dBot : Bot
  | titForTatBot : Bot
  | oBot : Bot
  | mirrorBot : Bot
  | eBot : Bot
  | cupodBot : Bot
  deriving DecidableEq, Repr

/-- Data structure holding both source and action for a bot. -/
structure BotData where
  source : SourceAST
  action : SourceAST → Action

/-- All bot definitions in one place. List each bot once. -/
def getBotData : Bot → BotData
  | Bot.cooperateBot => {
      source := PD.Models.Bots.CooperateBot.source,
      action := PD.Models.Bots.CooperateBot.action }
  | Bot.defectBot => {
      source := PD.Models.Bots.DefectBot.source,
      action := PD.Models.Bots.DefectBot.action }
  | Bot.dBot => {
      source := PD.Models.Bots.DBot.source,
      action := PD.Models.Bots.DBot.action }
  | Bot.titForTatBot => {
      source := PD.Models.Bots.TitForTatBot.source,
      action := PD.Models.Bots.TitForTatBot.action }
  | Bot.oBot => {
      source := PD.Models.Bots.OBot.source,
      action := PD.Models.Bots.OBot.action }
  | Bot.mirrorBot => {
      source := PD.Models.Bots.MirrorBot.source,
      action := PD.Models.Bots.MirrorBot.action }
  | Bot.eBot => {
      source := PD.Models.Bots.EBot.source,
      action := PD.Models.Bots.EBot.action }
  | Bot.cupodBot => {
      source := PD.Models.Bots.CupodBot.source,
      action := PD.Models.Bots.CupodBot.action }

/-- Generic lookup functions. -/
@[simp]
def botSource (b : Bot) : SourceAST := (getBotData b).source

@[simp]
def botAction (b : Bot) (oppSource : SourceAST) : Action := (getBotData b).action oppSource

/-- Source interpreter used by `ProgramModel` for this shared universe. -/
def botEvalSource (me : Bot) (oppSource : SourceAST) : Action :=
  botAction me oppSource

instance : ProgramModel Bot where
  SourceType := SourceAST
  source := botSource
  actionFromSource := botEvalSource

/-- Convenience wrapper around pipeline-dispatched action computation. -/
def botEval (me opp : Bot) : Action :=
  ProgramModel.action me opp

end PD.Models.BotUniverse

import PrisonersDilemma.Pipeline

namespace PD.Models.OpenSourceBots

open PD
open PD.Action

/-- Bot strategies in the open-source one-shot prisoner's dilemma. -/
inductive Bot : Type where
  | cooperateBot : Bot
  | defectBot : Bot
  | titForTat : Bot
  | suspiciousTFT : Bot
  | alternator : Bot
  deriving DecidableEq, Repr

instance : ProgramModel Bot where
  action
    | Bot.cooperateBot, _ => C
    | Bot.defectBot, _ => D
    | Bot.titForTat, Bot.cooperateBot => C
    | Bot.titForTat, Bot.titForTat => C
    | Bot.titForTat, Bot.alternator => C
    | Bot.titForTat, _ => D
    | Bot.suspiciousTFT, _ => D
    | Bot.alternator, Bot.cooperateBot => C
    | Bot.alternator, Bot.titForTat => C
    | Bot.alternator, _ => D

/-- Action chosen by a bot against an opponent bot. -/
def eval (me opp : Bot) : Action :=
  ProgramModel.action me opp

/-- Payoff for the row bot under the canonical PD payoff matrix. -/
def botPayoff (me opp : Bot) : Nat :=
  payoff canonicalPayoff (eval me opp) (eval opp me)

/-- Social welfare is the sum of both bots' payoffs. -/
def socialWelfare (me opp : Bot) : Nat :=
  botPayoff me opp + botPayoff opp me

end PD.Models.OpenSourceBots

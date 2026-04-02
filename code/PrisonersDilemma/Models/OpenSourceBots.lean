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

/-- Source-code encoding for each bot. Strategy rules reason about these strings
instead of matching opponent constructors directly. -/
@[simp] def cooperateBotSource : String := "C"
@[simp] def defectBotSource : String := "D"
@[simp] def titForTatSource : String := "CT"
@[simp] def suspiciousTFTSource : String := "DT"
@[simp] def alternatorSource : String := "CA"

@[simp]
def source : Bot → String
  | Bot.cooperateBot => cooperateBotSource
  | Bot.defectBot => defectBotSource
  | Bot.titForTat => titForTatSource
  | Bot.suspiciousTFT => suspiciousTFTSource
  | Bot.alternator => alternatorSource

/-- Source-level evaluator: my action given only opponent source text. -/
@[simp]
def evalSource (me : Bot) (oppSource : String) : Action :=
  match me with
  | Bot.cooperateBot => C
  | Bot.defectBot => D
  | Bot.titForTat =>
      if oppSource = cooperateBotSource || oppSource = titForTatSource ||
          oppSource = alternatorSource then
        C
      else
        D
  | Bot.suspiciousTFT => D
  | Bot.alternator => if oppSource = cooperateBotSource || oppSource = titForTatSource then C else D

instance : ProgramModel Bot where -- Define each bot's action as a function of opponent identity.
  SourceType := String
  source := source
  actionFromSource := evalSource

@[simp] theorem source_eq_source (b : Bot) :
  ProgramModel.source b = source b := rfl

@[simp] theorem actionFromSource_eq_evalSource (me : Bot) (oppSource : String) :
  ProgramModel.actionFromSource me oppSource = evalSource me oppSource := rfl

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

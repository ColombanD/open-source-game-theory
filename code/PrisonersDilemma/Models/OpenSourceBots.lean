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

instance : ProgramModel Bot where -- Define each bot's action as a function of opponent identity.
  action -- Implementation of the required `ProgramModel.action` method.
    | Bot.cooperateBot, _ => C -- Cooperator ignores opponent and plays `C`.
    | Bot.defectBot, _ => D -- Defector ignores opponent and plays `D`.
    | Bot.titForTat, Bot.cooperateBot => C -- Tit-for-tat cooperates with known cooperator.
    | Bot.titForTat, Bot.titForTat => C -- Tit-for-tat cooperates with itself.
    | Bot.titForTat, Bot.alternator => C -- Tit-for-tat cooperates with alternator in this encoding.
    | Bot.titForTat, _ => D -- Otherwise tit-for-tat defects.
    | Bot.suspiciousTFT, _ => D -- Suspicious TFT always defects in one-shot setting.
    | Bot.alternator, Bot.cooperateBot => C -- Alternator cooperates against cooperator.
    | Bot.alternator, Bot.titForTat => C -- Alternator cooperates against tit-for-tat.
    | Bot.alternator, _ => D -- Alternator defects against remaining opponents.

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

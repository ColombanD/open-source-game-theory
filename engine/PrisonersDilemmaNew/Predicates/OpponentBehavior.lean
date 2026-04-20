import PrisonersDilemmaNew.Models.Bot

namespace PDNew.Predicates.OpponentBehavior

open PDNew.Models.Bot

/-- Predicate: opponent is the canonical CooperateBot (identified by name). -/
def cooperatesAgainstCooperateBot (opp : BotInfo) : Prop :=
  if opp.name = "CooperateBot" then True
  else False

instance decidableCooperatesAgainstCooperateBot (opp : BotInfo) :
    Decidable (cooperatesAgainstCooperateBot opp) := by
  unfold cooperatesAgainstCooperateBot
  infer_instance

/-- Boolean view of the predicate for strategy-level branching. -/
def cooperatesAgainstCooperateBotB (opp : BotInfo) : Bool :=
  decide (cooperatesAgainstCooperateBot opp)

end PDNew.Predicates.OpponentBehavior

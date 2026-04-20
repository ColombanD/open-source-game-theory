import PrisonersDilemmaNew.Models.Bot
import PrisonersDilemmaNew.Predicates.OpponentBehavior

namespace PDNew.Models.Bot

open PDNew.Predicates.OpponentBehavior

def dBotStrategy(opp : BotInfo) : Action :=
  if cooperatesAgainstCooperateBot opp then Action.D else Action.C

def dBot : Bot :=
  { name := "DBot"
    source_code := "def dBotStrategy(opp.code) -> Action:\n    if cooperatesAgainstCooperateBot opp then Action.D else Action.C"
    strategy := dBotStrategy }

end PDNew.Models.Bot

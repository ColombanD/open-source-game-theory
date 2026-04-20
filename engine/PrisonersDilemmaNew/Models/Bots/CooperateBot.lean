import PrisonersDilemmaNew.Models.Bot

namespace PDNew.Models.Bot

def cooperateBotStrategy(_ : BotInfo) : Action := Action.C

def cooperateBotInfo : BotInfo :=
  { name := "CooperateBot"
    source_code := "def cooperateBotStrategy(opp.code) -> Action:\n    return Action.C" }

def cooperateBot : Bot :=
  { toBotInfo := cooperateBotInfo
    strategy := cooperateBotStrategy}

end PDNew.Models.Bot

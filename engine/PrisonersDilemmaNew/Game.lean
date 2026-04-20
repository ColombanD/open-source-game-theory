import PrisonersDilemmaNew.Models.Bot

open PDNew.Models.Bot
namespace PDNew

/-- Compute my action against an opponent from the opponent source code. -/
def playAction (me : Bot) (opp : BotInfo) : Action :=
  me.strategy opp

/-- Play both directions and return the ordered pair of actions. -/
def play (left right : Bot) : Action × Action :=
  (playAction left right.toBotInfo, playAction right left.toBotInfo)

end PDNew

namespace PDNew.Models.Bot

inductive Action : Type where
  | C : Action
  | D : Action
  deriving DecidableEq, Repr

structure BotInfo where
  name : String
  source_code : String -- readable by opponents
  deriving Repr

structure Bot extends BotInfo where
  strategy : BotInfo → Action

end PDNew.Models.Bot

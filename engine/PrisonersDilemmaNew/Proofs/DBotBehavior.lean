import PrisonersDilemmaNew.Models.Bots.DBot
import PrisonersDilemmaNew.Models.Bots.CooperateBot
import PrisonersDilemmaNew.Predicates.OpponentBehavior

namespace PDNew.Proofs.DBotBehavior

open PDNew.Models.Bot
open PDNew.Predicates.OpponentBehavior

theorem dBot_defects_against_cooperateBot :
    dBotStrategy cooperateBot.toBotInfo = Action.D := by
  unfold dBotStrategy
  simp
  unfold cooperatesAgainstCooperateBot
  unfold cooperateBot
  simp
  rfl

theorem dBot_defects_against_dBot :
    dBotStrategy dBot.toBotInfo = Action.C := by
  unfold dBotStrategy
  simp
  unfold cooperatesAgainstCooperateBot
  unfold dBot
  simp


end PDNew.Proofs.DBotBehavior

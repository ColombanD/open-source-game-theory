import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_MirrorBot_vs_OBot (n : Nat) :
    outcome (n+7) MirrorBot OBot = some (.D, .D) := by
  simp [outcome, play, eval, MirrorBot, OBot, CooperateBot, DefectBot, Prog.subst]
  decide

end PDNew.Theorems

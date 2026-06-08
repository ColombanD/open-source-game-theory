import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Dynamics

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_DefectBot_vs_TitForTatBot (n : Nat) :
    outcome (n+3) DefectBot TitForTatBot = some (.D, .D) := by
  simp [outcome, play, eval, TitForTatBot, DefectBot, Prog.subst]
  decide

end PDNew.Theorems

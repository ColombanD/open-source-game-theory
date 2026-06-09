import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DefectBot_vs_TitForTatBot (n : Nat) :
    outcome (n+3) DefectBot TitForTatBot = some (.D, .D) := by
  simp [outcome, play, eval, TitForTatBot, DefectBot, Prog.subst]
  decide

end PD.Theorems

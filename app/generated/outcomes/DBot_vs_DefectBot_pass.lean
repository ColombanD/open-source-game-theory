import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DBot_vs_DefectBot (n : Nat) :
    outcome (n+4) DBot DefectBot = some (.C, .D) := by
  simp [outcome, play, eval, DBot, DefectBot, Prog.subst]
  decide

end PD.Theorems

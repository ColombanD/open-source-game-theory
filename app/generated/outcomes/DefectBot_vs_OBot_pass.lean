import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.OBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DefectBot_vs_OBot (n : Nat) :
    outcome (n+5) DefectBot OBot = some (.D, .D) := by
  unfold outcome play
  simp [eval, OBot, DefectBot, Prog.subst]
  decide

end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.EBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DefectBot_vs_EBot (n : Nat) :
    outcome (n+5) DefectBot EBot = some (.D, .D) := by
  unfold outcome play
  simp [eval, EBot, DefectBot, Prog.subst]
  decide

end PD.Theorems

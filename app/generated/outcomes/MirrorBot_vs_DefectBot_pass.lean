import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_MirrorBot_vs_DefectBot (n : Nat) :
    outcome (n+3) MirrorBot DefectBot = some (.D, .D) := by
  simp [outcome, play, eval, MirrorBot, DefectBot, Prog.subst]

end PD.Theorems

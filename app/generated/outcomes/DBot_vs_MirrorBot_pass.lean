import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DBot_vs_MirrorBot (n : Nat) :
    outcome (n+6) DBot MirrorBot = some (.C, .C) := by
  simp [outcome, play, eval, DBot, MirrorBot, DefectBot, Prog.subst]
  decide

end PD.Theorems

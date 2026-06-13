import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_EBot_vs_EBot (n : Nat) :
    outcome (n+11) EBot EBot = some (.C, .C) := by
  simp [outcome, play, eval, EBot, MirrorBot, CooperateBot, DefectBot, Prog.subst,
        show (Action.C == Action.C) = true from rfl,
        show (Action.D == Action.C) = false from rfl]

end PD.Theorems

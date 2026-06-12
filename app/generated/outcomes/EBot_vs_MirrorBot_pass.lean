import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_EBot_vs_MirrorBot (n : Nat) :
    outcome (n+7) EBot MirrorBot = some (.C, .C) := by
  simp [outcome, play, eval, EBot, MirrorBot, CooperateBot, DefectBot, Prog.subst,
        show (Action.D == Action.C) = false from rfl,
        show (Action.C == Action.C) = true from rfl]

end PD.Theorems

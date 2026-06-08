import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_EBot_vs_MirrorBot (n : Nat) :
    outcome (n+7) EBot MirrorBot = some (.C, .C) := by
  simp [outcome, play, eval, EBot, MirrorBot, CooperateBot, DefectBot, Prog.subst,
        show (Action.D == Action.C) = false from rfl,
        show (Action.C == Action.C) = true from rfl]

end PDNew.Theorems

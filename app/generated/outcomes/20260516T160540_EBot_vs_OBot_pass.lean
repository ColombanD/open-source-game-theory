import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_EBot_vs_OBot (n : Nat) :
    outcome (n+8) EBot OBot = some (.C, .D) := by
  have h1 : (Action.D == Action.C) = false := rfl
  have h2 : (Action.C == Action.C) = true := rfl
  simp [outcome, play, eval, EBot, OBot, Prog.subst, DefectBot, CooperateBot, MirrorBot, h1, h2]

end PDNew.Theorems

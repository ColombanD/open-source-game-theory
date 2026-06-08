import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.MirrorBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_DBot_vs_EBot (n : Nat) :
    outcome (n+8) DBot EBot = some (.C, .D) := by
  unfold outcome play
  have h1 : (Action.D == Action.C) = false := rfl
  have h2 : (Action.C == Action.C) = true := rfl
  simp [eval, DBot, EBot, DefectBot, CooperateBot, MirrorBot, Prog.subst, h1, h2]

end PDNew.Theorems

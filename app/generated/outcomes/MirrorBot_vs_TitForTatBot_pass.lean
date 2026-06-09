import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_MirrorBot_vs_TitForTatBot (n : Nat) :
    outcome (n+6) MirrorBot TitForTatBot = some (.C, .C) := by
  unfold outcome play
  simp [MirrorBot, TitForTatBot, CooperateBot, eval, Prog.subst]
  decide

end PD.Theorems

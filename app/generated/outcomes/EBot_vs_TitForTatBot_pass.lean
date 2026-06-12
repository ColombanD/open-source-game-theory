import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_EBot_vs_TitForTatBot (n : Nat) :
    outcome (n+10) EBot TitForTatBot = some (.C, .D) := by
  unfold outcome play
  simp [eval, EBot, TitForTatBot, CooperateBot, DefectBot, MirrorBot, Prog.subst]
  decide

end PD.Theorems

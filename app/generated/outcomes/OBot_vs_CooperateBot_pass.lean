import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_OBot_vs_CooperateBot (n : Nat) :
    outcome (n+5) OBot CooperateBot = some (.C, .C) := by
  unfold outcome play
  simp [eval, OBot, CooperateBot, Prog.subst]
  decide

end PD.Theorems

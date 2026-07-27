import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_DBot_vs_CooperateBot (n : Nat) :
    outcome (n+3) DBot CooperateBot = some (.D, .C) := by
  unfold outcome play DBot CooperateBot
  simp [eval, Prog.subst]
  decide

end PD.Theorems

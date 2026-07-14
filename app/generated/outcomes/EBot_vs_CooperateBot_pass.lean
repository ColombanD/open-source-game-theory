import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_EBot_vs_CooperateBot (n : Nat) :
    outcome (n+3) EBot CooperateBot = some (.D, .C) := by
  have hA : play (n+3) EBot CooperateBot = some .D := by
    show eval (n+3) EBot CooperateBot EBot = some .D
    unfold EBot
    simp [eval, Prog.subst, CooperateBot, show (Action.C == Action.C) = true from rfl]
  have hB : play (n+3) CooperateBot EBot = some .C := rfl
  simp [outcome, hA, hB]

end PD.Theorems

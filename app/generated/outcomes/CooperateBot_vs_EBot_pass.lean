import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.EBot

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_EBot (n : Nat) :
    outcome (n+3) CooperateBot EBot = some (.C, .D) := by
  have hA : play (n+3) CooperateBot EBot = some .C := rfl
  have hB : play (n+3) EBot CooperateBot = some .D := by
    show eval (n+3) EBot CooperateBot EBot = some .D
    unfold EBot CooperateBot
    simp [eval, Prog.subst]
    intro h
    exact absurd h (by decide)
  simp [outcome, hA, hB]

end PD.Theorems

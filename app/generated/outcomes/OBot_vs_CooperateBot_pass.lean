import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_OBot_vs_CooperateBot (n : Nat) :
    outcome (n+5) OBot CooperateBot = some (.C, .C) := by
  have hA : play (n+5) OBot CooperateBot = some .C := by
    show eval (n+5) OBot CooperateBot OBot = some .C
    unfold OBot CooperateBot
    simp [eval, Prog.subst]
    decide
  have hB : play (n+5) CooperateBot OBot = some .C := rfl
  simp [outcome, hA, hB]

end PD.Theorems

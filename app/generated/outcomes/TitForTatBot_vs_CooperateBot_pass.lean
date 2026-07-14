import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_TitForTatBot_vs_CooperateBot (n : Nat) :
    outcome (n+3) TitForTatBot CooperateBot = some (.C, .C) := by
  have hA : play (n+3) TitForTatBot CooperateBot = some .C := by
    show eval (n+3) TitForTatBot CooperateBot TitForTatBot = some .C
    unfold TitForTatBot CooperateBot
    simp [eval, Prog.subst]
    decide
  have hB : play (n+3) CooperateBot TitForTatBot = some .C := rfl
  simp [outcome, hA, hB]

end PD.Theorems

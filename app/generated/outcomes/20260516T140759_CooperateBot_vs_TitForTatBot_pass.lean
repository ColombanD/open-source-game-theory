import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.TitForTatBot

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

theorem llm_outcome_CooperateBot_vs_TitForTatBot (n : Nat) :
    outcome (n+3) CooperateBot TitForTatBot = some (.C, .C) := by
  have hA : play (n+3) CooperateBot TitForTatBot = some .C := rfl
  have hB : play (n+3) TitForTatBot CooperateBot = some .C := by
    show eval (n+3) TitForTatBot CooperateBot TitForTatBot = some .C
    unfold TitForTatBot CooperateBot
    simp [eval, Prog.subst]
    decide
  simp [outcome, hA, hB]

end PDNew.Theorems

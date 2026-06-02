import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics

open PDNew
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_CooperateBot_vs_OBot (n : Nat) :
    outcome (n+5) CooperateBot OBot = some (.C, .C) := by
  have hA : play (n+5) CooperateBot OBot = some .C := rfl
  have hB : play (n+5) OBot CooperateBot = some .C := by
    show eval (n+5) OBot CooperateBot OBot = some .C
    unfold OBot CooperateBot
    simp [eval, Prog.subst]
    decide
  simp [outcome, hA, hB]

end PDNew.Theorems

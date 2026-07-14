import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_MirrorBot_vs_CooperateBot (n : Nat) :
    outcome (n+3) MirrorBot CooperateBot = some (.C, .C) := by
  have hA : play (n+3) MirrorBot CooperateBot = some .C := by
    show eval (n+3) MirrorBot CooperateBot MirrorBot = some .C
    simp [eval, MirrorBot, CooperateBot, Prog.subst]
  have hB : play (n+3) CooperateBot MirrorBot = some .C := rfl
  simp [outcome, hA, hB]

end PD.Theorems

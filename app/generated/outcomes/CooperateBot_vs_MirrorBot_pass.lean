import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.MirrorBot

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_MirrorBot (n : Nat) :
    outcome (n+3) CooperateBot MirrorBot = some (.C, .C) := by
  have hA : play (n+3) CooperateBot MirrorBot = some .C := rfl
  have hB : play (n+3) MirrorBot CooperateBot = some .C := by
    show eval (n+3) MirrorBot CooperateBot MirrorBot = some .C
    simp [eval, MirrorBot, Prog.subst, CooperateBot]
  simp [outcome, hA, hB]

end PD.Theorems

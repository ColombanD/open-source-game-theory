import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_EBot_vs_CooperateBot (n : Nat) :
    outcome (n+3) EBot CooperateBot = some (.D, .C) := by
  have hA : play (n+3) EBot CooperateBot = some Action.D := by
    show eval (n+3) EBot CooperateBot EBot = some Action.D
    unfold EBot
    simp only [eval, Prog.subst, CooperateBot]
    show ((eval (n+1) (.const Action.C) (.bot DefectBot) (.const Action.C)).bind _) = some Action.D
    simp only [eval, Option.bind_some]
    rfl
  have hB : play (n+3) CooperateBot EBot = some Action.C := rfl
  simp [outcome, hA, hB]

end PD.Theorems

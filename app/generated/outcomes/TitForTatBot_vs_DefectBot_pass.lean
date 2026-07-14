import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_TitForTatBot_vs_DefectBot (n : Nat) :
    outcome (n+3) TitForTatBot DefectBot = some (.D, .D) := by
  have hA : play (n+3) TitForTatBot DefectBot = some .D := by
    show eval (n+3) TitForTatBot DefectBot TitForTatBot = some .D
    simp [eval, TitForTatBot, DefectBot, Prog.subst, CooperateBot, show (Action.D == Action.C) = false from rfl]
  have hB : play (n+3) DefectBot TitForTatBot = some .D := rfl
  simp [outcome, hA, hB]

end PD.Theorems

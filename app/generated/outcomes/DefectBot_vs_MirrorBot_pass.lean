import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot

open PD
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_DefectBot_vs_MirrorBot (n : Nat) :
    outcome (n+2) DefectBot MirrorBot = some (.D, .D) := by
  have hA : play (n+2) DefectBot MirrorBot = some .D := by
    unfold play DefectBot
    rfl
  have hB : play (n+2) MirrorBot DefectBot = some .D := by
    unfold play MirrorBot DefectBot
    simp [eval, Prog.subst]
  simp [outcome, hA, hB]

end PD.Theorems

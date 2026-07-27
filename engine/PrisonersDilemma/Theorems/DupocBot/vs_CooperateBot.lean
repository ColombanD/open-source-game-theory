import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs CooperateBot: uses proof search being true -/
theorem outcome_DupocBot_vs_CooperateBot (fuel : Nat):
    ∃ k, outcome (fuel + 2) (DupocBot k) CooperateBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_CooperateBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (DupocBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (DupocBot k) CooperateBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) CooperateBot (DupocBot k) = some .C := by
    simpa [Nat.add_assoc] using (play_CooperateBot (fuel + 1) (DupocBot k))

  simp [outcome, hA, hB]

end PD.Theorems

import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- DupocBot vs CooperateBot: uses proof search being true -/
@[outcome]
theorem outcome_DupocBot_vs_CooperateBot :
    OutcomeSpec .eventual 2
      DupocBot (fun _ => CooperateBot) (some (.C, .C)) := by
  -- The guard's certificate now pays the atom's size (`Nat.log2 k + 10`, the recost of
  -- 2026-09-16), so the threshold comes from `linear_log2_add_le`, not a literal.
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 10
  refine ⟨K, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_CooperateBot_ge k (by have := hK k (Nat.le_of_lt hlt); omega)

  have hA : play (fuel + 2) (DupocBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (DupocBot k) CooperateBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) CooperateBot (DupocBot k) = some .C := by
    simpa [Nat.add_assoc] using (play_CooperateBot (fuel + 1) (DupocBot k))

  simp [outcome, hA, hB]

end PD.Theorems

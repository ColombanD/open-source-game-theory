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
  refine ⟨atom_cost 1, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_CooperateBot_ge k (Nat.le_of_lt hlt)

  have hA : play (fuel + 2) (DupocBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (DupocBot k) CooperateBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) CooperateBot (DupocBot k) = some .C := by
    simpa [Nat.add_assoc] using (play_CooperateBot (fuel + 1) (DupocBot k))

  simp [outcome, hA, hB]

end PD.Theorems

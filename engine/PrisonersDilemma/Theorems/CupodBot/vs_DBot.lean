import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodBot vs DBot: mutual cooperation. -/
@[outcome]
theorem outcome_CupodBot_vs_DBot :
    OutcomeSpec .eventual 4
      CupodBot (fun _ => DBot) (some (.C, .C)) := by
  refine ⟨atom_cost 2, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_bot_DefectBot_ge k (Nat.le_of_lt hlt)
  have hA : play (fuel + 4) (CupodBot k) DBot = some .C := by
    have hg := proofSearch_false_for_DBot k hk
    show eval (fuel + 4) (CupodBot k) DBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) DBot (CupodBot k) = some .C := by
    exact DBot_plays_C_against_CupodBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

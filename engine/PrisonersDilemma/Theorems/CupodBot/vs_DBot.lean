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
  -- The `.bot DefectBot` certificate pays the atom's size (`Nat.log2 k + 12`, the
  -- recost of 2026-09-16), so the threshold comes from `linear_log2_add_le`.
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 12
  refine ⟨K, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_bot_DefectBot_ge k (by have := hK k (Nat.le_of_lt hlt); omega)
  have hA : play (fuel + 4) (CupodBot k) DBot = some .C := by
    have hg := proofSearch_false_for_DBot k hk
    show eval (fuel + 4) (CupodBot k) DBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) DBot (CupodBot k) = some .C := by
    exact DBot_plays_C_against_CupodBot k fuel hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

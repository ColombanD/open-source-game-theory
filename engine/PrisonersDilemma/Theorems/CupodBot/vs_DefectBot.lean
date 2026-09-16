import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodBot vs DefectBot: uses proof search being true -/
@[outcome]
theorem outcome_CupodBot_vs_DefectBot :
    OutcomeSpec .eventual 2
      CupodBot (fun _ => DefectBot) (some (.D, .D)) := by
  -- The guard's certificate now pays the atom's size (`Nat.log2 k + 10`, the recost of
  -- 2026-09-16), so the threshold comes from `linear_log2_add_le`, not a literal.
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 10
  refine ⟨K, fun k hlt fuel => ?_⟩
  have hk := proofSearch_true_for_DefectBot_ge k (by have := hK k (Nat.le_of_lt hlt); omega)

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D := by
    show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  simp [outcome, hA, hB]

end PD.Theorems

import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

-- Full determination: given the ONLY missing fact (self-D unprovable), (C,D) follows.
theorem optim_db_outerC_false (k : Nat) :
    proofSearch k (Formula.plays DefectBot (OptimBot k k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (OptimBot k k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

theorem optim_db_r3outer_true (k : Nat) (hk : 1 ≤ k) :
    proofSearch k (Formula.plays DefectBot (OptimBot k k) Action.D) = true := by
  have hcert : AtomProvable 1 (.plays DefectBot (OptimBot k k) Action.D) :=
    ⟨(PlaysProof.const : PlaysProof DefectBot (OptimBot k k) (.const Action.D) Action.D c_leaf),
     by simp [c_leaf]⟩
  exact (proofSearch_spec k _).2 (Pf_mono (Pf.atom hcert) hk)

theorem optim_db_plays_C_of_selfD_false (k fuel : Nat) (hk : 1 ≤ k)
    (hR3inner : proofSearch k (Formula.plays (OptimBot k k) DefectBot Action.D) = false) :
    play (fuel + 8) (OptimBot k k) DefectBot = some .C := by
  have hOuterC := optim_db_outerC_false k
  have hR3outer := optim_db_r3outer_true k hk
  show eval (fuel + 8) (OptimBot k k) DefectBot (OptimBot k k) = some .C
  unfold OptimBot at hOuterC hR3outer hR3inner ⊢
  simp [eval, Prog.subst, Formula.subst, hOuterC, hR3outer, hR3inner]

-- DefectBot plays D vs OptimBot (always)
theorem optim_db_defect_plays_D (k fuel : Nat) :
    play (fuel + 8) DefectBot (OptimBot k k) = some .D := by
  simpa [Nat.add_comm] using play_DefectBot (fuel + 7) (OptimBot k k)

-- Thus: CONDITIONALLY on self-D being unprovable, outcome = (C,D).
theorem optim_db_outcome_C_D_of_selfD_false (k fuel : Nat) (hk : 1 ≤ k)
    (hR3inner : proofSearch k (Formula.plays (OptimBot k k) DefectBot Action.D) = false) :
    outcome (fuel + 8) (OptimBot k k) DefectBot = some (.C, .D) := by
  have hA := optim_db_plays_C_of_selfD_false k fuel hk hR3inner
  have hB := optim_db_defect_plays_D k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

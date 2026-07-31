import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_LegibleBot_vs_CupodBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (CupodBot k) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun k => CupodBot k) 100
    (fun k => by
      show (CupodBot k).size ≤ 100 + 20 * Nat.log2 k
      simp only [CupodBot, Prog.size, Formula.size, numCost]; omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hLeg : play n (LegibleBot (2*k+64) k) (CupodBot k) = some .C := hn
  -- LegibleBot never plays D against CupodBot
  have hInterpFalse : ¬ (Formula.plays (LegibleBot (2*k+64) k) (CupodBot k) .D).interp := by
    rintro ⟨m, hm⟩
    have hLeg' : play (max n m) (LegibleBot (2*k+64) k) (CupodBot k) = some .C :=
      eval_mono_le hLeg _ (Nat.le_max_left _ _)
    have hm' : play (max n m) (LegibleBot (2*k+64) k) (CupodBot k) = some .D :=
      eval_mono_le hm _ (Nat.le_max_right _ _)
    rw [hLeg'] at hm'
    cases hm'
  -- proofSearch for CupodBot's defect guard fails
  have hSearchFalse : proofSearch k
      (.plays (LegibleBot (2*k+64) k) (CupodBot k) .D) = false := by
    cases hps : proofSearch k (.plays (LegibleBot (2*k+64) k) (CupodBot k) .D) with
    | true => exact absurd (proofSearch_sound _ _ hps) hInterpFalse
    | false => rfl
  -- CupodBot plays C (guard fails)
  have hCup : play (n + 2) (CupodBot k) (LegibleBot (2*k+64) k) = some .C := by
    show eval (n + 2) (CupodBot k) (LegibleBot (2*k+64) k) (CupodBot k) = some .C
    unfold CupodBot at hSearchFalse ⊢
    simp [eval, Prog.subst, Formula.subst, hSearchFalse]
  have hLeg2 : play (n + 2) (LegibleBot (2*k+64) k) (CupodBot k) = some .C :=
    eval_mono_le hLeg _ (Nat.le_add_right _ _)
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hLeg2 hCup⟩

end PD.Theorems

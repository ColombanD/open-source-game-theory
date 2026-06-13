import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Axioms

open PD
open PD.Bots
open PD.Axioms

namespace PD.Theorems

/-- Auxiliary: given proofSearch evidence on the inner DefectBot probe,
    OBot defects against CupodBot. -/
private theorem llm_OBot_plays_D_vs_CupodBot_aux
    (n k : Nat)
    (hInner : proofSearch k (.plays (.bot DefectBot) (CupodBot k) Action.D) = true) :
    play (n + 6) OBot (CupodBot k) = some Action.D := by
  have hCB : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) Action.D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) Action.D) with
    | true =>
        exfalso
        exact interp_bot_CooperateBot_plays_D_false (CupodBot k)
          (proofSearch_sound k _ h)
    | false => rfl
  have hGuard1 : eval (n+5) OBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some Action.C := by
    show eval (n+4) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some Action.C
    show (if proofSearch k (Formula.plays (.bot CooperateBot) (CupodBot k) Action.D)
          then eval (n+3) (CupodBot k) (.bot CooperateBot) (.const Action.D)
          else eval (n+3) (CupodBot k) (.bot CooperateBot) (.const Action.C)) = some Action.C
    rw [hCB]
    rfl
  have hGuard2 : eval (n+4) OBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some Action.D := by
    show eval (n+3) (CupodBot k) (.bot DefectBot) (CupodBot k) = some Action.D
    show (if proofSearch k (Formula.plays (.bot DefectBot) (CupodBot k) Action.D)
          then eval (n+2) (CupodBot k) (.bot DefectBot) (.const Action.D)
          else eval (n+2) (CupodBot k) (.bot DefectBot) (.const Action.C)) = some Action.D
    rw [hInner]
    rfl
  have hPlay := play_ite_from_guard
      n 5 OBot (CupodBot k) (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      (.const Action.D)
      Action.C Action.C
      (by unfold OBot; rfl) hGuard1
  have hInnerIte :
      eval (n+5) OBot (CupodBot k)
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
      = some Action.D := by
    rw [show n+5 = n+4+1 from rfl]
    rw [eval_ite_from_guard (n+4) OBot (CupodBot k) (.sim .opp (.bot DefectBot))
        (.const Action.C) (.const Action.D) Action.C Action.D hGuard2]
    rfl
  show play (n+5+1) OBot (CupodBot k) = some Action.D
  rw [hPlay]
  exact hInnerIte

/-- Auxiliary: given proofSearch evidence on OBot's defection, CupodBot defects. -/
private theorem llm_CupodBot_plays_D_vs_OBot_aux
    (n k : Nat)
    (hOuter : proofSearch k (.plays OBot (CupodBot k) Action.D) = true) :
    play (n + 6) (CupodBot k) OBot = some Action.D := by
  show eval (n+6) (CupodBot k) OBot (CupodBot k) = some Action.D
  show (if proofSearch k (Formula.plays OBot (CupodBot k) Action.D)
        then eval (n+5) (CupodBot k) OBot (.const Action.D)
        else eval (n+5) (CupodBot k) OBot (.const Action.C)) = some Action.D
  rw [hOuter]
  rfl

/-- Main theorem (existential): for sufficiently large search budget `k`,
    CupodBot defects against OBot and OBot defects against CupodBot. -/
theorem llm_outcome_CupodBot_vs_OBot :
    ∃ K FUEL : Nat, ∀ k, K ≤ k → ∀ n, outcome (n + FUEL) (CupodBot k) OBot = some (.D, .D) := by
  have hPlayDB0 : ∃ m, play m (.bot DefectBot) (CupodBot 0) = some Action.D := by
    refine ⟨2, ?_⟩
    show eval 2 (.bot DefectBot) (CupodBot 0) (.bot DefectBot) = some Action.D
    unfold DefectBot
    rfl
  obtain ⟨w₁, hw₁⟩ := witness_complete_plays (.bot DefectBot) (CupodBot 0) Action.D hPlayDB0
  have hInner_all : ∀ k, witnessChars w₁ ≤ k →
      proofSearch k (.plays (.bot DefectBot) (CupodBot k) Action.D) = true := by
    intro k hk
    obtain ⟨w', hw', hsize⟩ := witness_transport_family
      (fun k => Formula.plays (.bot DefectBot) (CupodBot k) Action.D)
      0 k (Nat.zero_le _) w₁ hw₁ hk
    exact (proofSearch_spec k _).2 ⟨w', hw', hsize⟩
  have hPlay_OBot : ∃ m, play m OBot (CupodBot (witnessChars w₁)) = some Action.D :=
    ⟨6, llm_OBot_plays_D_vs_CupodBot_aux 0 (witnessChars w₁) (hInner_all _ (Nat.le_refl _))⟩
  obtain ⟨w₂, hw₂⟩ :=
    witness_complete_plays OBot (CupodBot (witnessChars w₁)) Action.D hPlay_OBot
  have hOuter_all : ∀ k, witnessChars w₁ ≤ k → witnessChars w₂ ≤ k →
      proofSearch k (.plays OBot (CupodBot k) Action.D) = true := by
    intro k hk1 hk2
    obtain ⟨w', hw', hsize⟩ := witness_transport_family
      (fun k => Formula.plays OBot (CupodBot k) Action.D)
      (witnessChars w₁) k hk1 w₂ hw₂ hk2
    exact (proofSearch_spec k _).2 ⟨w', hw', hsize⟩
  refine ⟨max (witnessChars w₁) (witnessChars w₂), 6, ?_⟩
  intro k hk n
  have hk1 : witnessChars w₁ ≤ k := Nat.le_trans (Nat.le_max_left _ _) hk
  have hk2 : witnessChars w₂ ≤ k := Nat.le_trans (Nat.le_max_right _ _) hk
  have hI := hInner_all k hk1
  have hO := hOuter_all k hk1 hk2
  have hA := llm_CupodBot_plays_D_vs_OBot_aux n k hO
  have hB := llm_OBot_plays_D_vs_CupodBot_aux n k hI
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

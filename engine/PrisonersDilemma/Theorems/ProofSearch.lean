import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms

open PDNew
open PDNew.Axioms
namespace PDNew.Theorems

-- Soundness of bounded proof search.
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp := by
  intro k φ hk
  obtain ⟨w, hw, _⟩ := (proofSearch_spec k φ).1 hk
  exact witness_sound w φ hw

/-- Completeness of bounded proof search for atomic plays-formulas. -/
theorem proofSearch_complete_plays :
∀ p q a, (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a h
  obtain ⟨w, hw⟩ := witness_complete_plays p q a h
  refine ⟨witnessChars w, ?_⟩
  exact (proofSearch_spec (witnessChars w) (.plays p q a)).2 ⟨w, hw, Nat.le_refl _⟩

-- Monotonicity in proof-search budget.
theorem proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true := by
  intro k₁ k₂ φ hk h1
  obtain ⟨w, hw, hk1⟩ := (proofSearch_spec k₁ φ).1 h1
  exact (proofSearch_spec k₂ φ).2 ⟨w, hw, Nat.le_trans hk1 hk⟩

end PDNew.Theorems

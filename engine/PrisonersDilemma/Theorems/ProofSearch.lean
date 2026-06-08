import PrisonersDilemma.Derivation
import PrisonersDilemma.Axioms

open PDNew
open PDNew.Axioms
namespace PDNew.Theorems

-- Soundness of bounded proof search. Either the formula is provable by the
-- structural `Derivation` rules (→ `Derivation.sound`), or it is an atomic σ₁
-- fact (→ `AtomProvable_sound`).
theorem proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp := by
  intro k φ hk
  rcases (proofSearch_spec k φ).1 hk with ⟨d, _⟩ | hatom
  · exact d.sound
  · exact AtomProvable_sound φ hatom

/-- Completeness of bounded proof search for atomic plays-formulas, via the
    σ₁ atom-completeness axiom. Any budget works (`AtomProvable` is
    budget-independent); pick `0`. -/
theorem proofSearch_complete_plays :
∀ p q a, (∃ n, play n p q = some a) → ∃ k, proofSearch k (.plays p q a) = true := by
  intro p q a h
  exact ⟨0, (proofSearch_spec 0 (.plays p q a)).2 (Or.inr (atom_complete p q a h))⟩

-- Monotonicity in proof-search budget: the structural disjunct relaxes its size
-- bound, and the `AtomProvable` disjunct is budget-independent — so both carry
-- over to any larger budget.
theorem proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true := by
  intro k₁ k₂ φ hk h1
  rcases (proofSearch_spec k₁ φ).1 h1 with ⟨d, hd⟩ | hatom
  · exact (proofSearch_spec k₂ φ).2 (Or.inl ⟨d, Nat.le_trans hd hk⟩)
  · exact (proofSearch_spec k₂ φ).2 (Or.inr hatom)

end PDNew.Theorems

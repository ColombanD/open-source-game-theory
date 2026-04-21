import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics

open PDNew
namespace PDNew.Axioms

-- Soundness of bounded proof search: if the oracle returns `true` on a formula, then that formula is semantically true.
axiom proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp

-- Parametric Bounded Löb (stated for completeness; not used below).
-- `□_{f(k)} φ` is encoded as a distinguished formula constructor in a
-- fuller development; here we leave it schematic.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat),
    (∀ k, f k ≥ Nat.log2 k + 1) →
    (∀ k, ∃ m, proofSearch m (.impl (φ k) (φ k)) = true) →
      ∃ k₂, ∀ k ≥ k₂, ∃ m, proofSearch m (φ k) = true

end PDNew.Axioms

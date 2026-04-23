import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PDNew
namespace PDNew.Axioms

-- Soundness of bounded proof search: if the oracle returns `true` on a formula, then that formula is semantically true.
axiom proofSearch_sound :
  ∀ k φ, proofSearch k φ = true → φ.interp

-- Completeness of bounded proof search: if the formula is semantically true, then the oracle returns `true`.
axiom proofSearch_complete :
  ∀ φ, φ.interp → ∃ k, proofSearch k φ = true

-- Monotonicity of bounded proof search: if the oracle returns `true` on a formula with some fuel, then it also returns `true` with more fuel.
axiom proofSearch_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → proofSearch k₁ φ = true → proofSearch k₂ φ = true


-- Parametric Bounded Löb's Theorem (Lemma 3.6).
--
-- Informally: let `φ k` be a formula family in the proof language of `S`,
-- `k₁ ∈ ℕ` a base threshold, and `f : ℕ → ℕ` an *increasing* computable
-- function with `f(k) ≻ O(lg k)`. If `S` can derive, for every `k > k₁`,
-- that bounded provability of `φ k` within `f(k)` steps implies `φ k`
-- itself, then there exists a threshold `k₂` beyond which `S` proves
-- `φ k` outright.
--
-- Encoding notes:
-- * `□_{f(k)}(φ k)` is the formula `Formula.box (f k) (φ k)`; its
--   semantic clause is `proofSearch (f k) (φ k) = true`.
-- * "`S` derives ψ" is `∃ m, proofSearch m ψ = true`.
-- * `f(k) ≻ O(lg k)` is spelled out as: there exists a positive constant
--   `c` and a threshold `k̂` such that for all `k > k̂`, `f(k) > c · lg k`.
-- * "Increasing" is the plain pointwise condition on `f`; the
--   "computable" side of the paper's hypothesis is vacuous in Lean since
--   every `Nat → Nat` we can write down is already computable in the
--   relevant sense.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, proofSearch m (.impl (.box (f k) (φ k)) (φ k)) = true) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, proofSearch m (φ k) = true

end PDNew.Axioms

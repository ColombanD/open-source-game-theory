import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PD
namespace PD.Axioms

/-!
# Axioms

Principles of `S` not discharged constructively. Four remain:

* `c_guard_mono` — the opaque `c_guard` cost function is monotone in `k`.
* `atom_complete_false_guard` — the irreducible Π₁ residue: a play that branches
  on a *failed* guard has a certificate. Everything else is a theorem.
* `box_provable` — bounded GL axiom 4 (HBL D2); currently unused.
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6).

Everything else is a theorem in `BaseTheorems.lean`.
-/

/-- `c_guard` (the cost of writing the budget numeral `k` in a proof transcript)
    is monotone: a larger `k` takes at least as many characters to write.
    Needed for `atom_cost_mono`. -/
axiom c_guard_mono : ∀ {a b : Nat}, a ≤ b → c_guard a ≤ c_guard b

/-- The irreducible Π₁ residue of σ₁-completeness: a play that has no
    constructive `PlaysProof` certificate (because it branched on a *failed*
    proof search, requiring `¬ Provable k (guard)` — Π₁, non-positive) still
    has an `AtomProvable` certificate at budget `atom_cost fuel`.
    Use `atom_complete` (the theorem below) at call sites. -/
axiom atom_complete_false_guard :
  ∀ p q a fuel, play fuel p q = some a →
    ¬ (∃ _ : PlaysProof p q p a (atom_cost fuel), True) →
    AtomProvable (atom_cost fuel) (.plays p q a)

/-- Bounded GL axiom 4 (`□_k φ → □_K □_k φ`): if `φ` is provable within budget
    `k`, then that fact is itself provable at some larger budget `K`. Sound by
    Solovay / HBL D2; axiomatic here because the budget-indexed box makes a
    constructive witness impossible without size-indexing `Derivation`. Currently
    unused. -/
axiom box_provable :
  ∀ (k : Nat) (φ : Formula), Provable k φ → ∃ K, Provable K (.box k φ)

-- Parametric Bounded Löb Theorem (critch22 Lemma 3.6).
--
-- If `f(k) ≻ O(log k)` and S proves `□_{f(k)} φ(k) → φ(k)` for all large k,
-- then S proves `φ(k)` outright for all large k.
--
-- The hypothesis is *unbudgeted* (`∃ m, Provable m …`) — faithful to Critch's
-- `⊢`, which carries no size annotation on the implication proof. Consumers
-- (CupodBot, DupocBot) supply the `f(k) ≻ O(log k)` bound separately via
-- `linear_log2_add_le` and `Derivation.size`.
--
-- We use the per-instance meta-∀ (`∀ k > k₁, ∃ m, Provable m …`) rather than
-- Critch's single universally-quantified object-formula, because `Formula` has
-- no internal ∀ quantifier. This is implied by Critch's statement and sufficient
-- for all consumers.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k)

end PD.Axioms

import PrisonersDilemma.Program
import PrisonersDilemma.Derivation

open PDNew
namespace PDNew.Axioms

/-!
# Surviving axioms

After the reform that made the proof system `S` semi-explicit
(`Derivation.lean`), the bespoke proof-system axioms collapsed to:

* the explicit `Derivation` system + its proved soundness (`Derivation.sound`),
* `proofSearch` as a *definition* (`decide ∘ Provable`) with `proofSearch_spec`
  a *theorem*,
* the source-transparency steps as *theorems* (`proof_system_verifies_*`).

What remains genuinely axiomatic lives here or in `Derivation.lean`:

* `Derivation.atom_complete` / `AtomProvable_sound` — σ₁-completeness and
  soundness for atomic `.plays` formulas (cannot be made constructive without
  recreating the `play`/`proofSearch` cycle).
* `PBLT` (below) — the Parametric Bounded Löb Theorem, borrowed from critch22.
* `Provable_transport_family` (below) — CUPOD/DUPOC monotonicity under growing
  bot index. **Out of scope** for this reform; its general form is not
  derivable at the play level (an opponent can behave differently against
  `CupodBot n` vs `CupodBot k`). Flagged for separate, per-opponent treatment.
-/

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
--   semantic clause is `Provable (f k) (φ k)`.
-- * "`S` derives ψ" is `∃ m, proofSearch m ψ = true`.
-- * `f(k) ≻ O(lg k)` is spelled out as: there exists a positive constant
--   `c` and a threshold `k̂` such that for all `k > k̂`, `f(k) > c · lg k`.
-- * "Increasing" is the plain pointwise condition on `f`.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, proofSearch m (.impl (.box (f k) (φ k)) (φ k)) = true) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, proofSearch m (φ k) = true

/--
Transport of provability across a parameterized formula family when the
parameter grows: if `Φ n` is provable within budget `k` and `n ≤ k`, then so is
`Φ k`.

This is the one assumption this reform deliberately does **not** discharge. It
is used only for CUPOD/DUPOC monotonicity (`CupodBot_monotonicity`,
`DupocBot_monotonicity`), where `Φ i = plays Bot (CupodBot i) a`. Its general
form (arbitrary opponent `Bot`) is genuinely not derivable at the play level —
an opponent may behave differently against `CupodBot n` vs `CupodBot k` — so
eliminating it requires per-opponent restructuring, tracked as separate work.

Restated over `Provable` (was `witness_transport_family`, over the now-deleted
abstract witness interface).
-/
axiom Provable_transport_family :
  ∀ (Φ : Nat → Formula) n k, n ≤ k → Provable k (Φ n) → Provable k (Φ k)

end PDNew.Axioms

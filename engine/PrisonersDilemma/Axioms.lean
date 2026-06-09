import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PD
namespace PD.Axioms

/-!
# Surviving axioms

After the reform that made the proof system `S` semi-explicit
(`Derivation.lean`), the bespoke proof-system axioms collapsed to:

* the explicit `Derivation` system + its proved soundness (`Derivation.sound`),
* `proofSearch` as a *definition* (`decide ∘ Provable`) with `proofSearch_spec`
  a *theorem*,
* the source-transparency steps as *theorems* (`proof_system_verifies_*`). -/

/-- σ₁-completeness for atoms, **budget-sensitive**: a true atomic play is
    provable in S, but only once the budget is large enough — there is *some*
    threshold `K` (the proof cost) at which it becomes provable. critch22 uses
    σ₁-completeness implicitly (e.g. "CUPOD(10⁹)(DB.source) will find the proof
    and return D"); it is decidable Σ₁ truth, no Gödel obstruction.

    The `∃ K` (rather than provability at *every* budget) is what lets a true
    play be *unprovable within a too-small budget* — the slack Open Problem 3's
    `outcome(DUPOC,CUPOD) = (D,C)` requires. -/
axiom atom_complete :
  ∀ p q a, (∃ n, play n p q = some a) → ∃ K, AtomProvable K (.plays p q a)

/-- Atom provability is monotone in budget: more characters never hurt. With the
    budget index this must be stated (it was automatic before). -/
axiom atom_monotone :
  ∀ k₁ k₂ φ, k₁ ≤ k₂ → AtomProvable k₁ φ → AtomProvable k₂ φ

/-- S is sound on atoms. Companion to `atom_complete`; the atomic analogue of
    `Derivation.sound`, needed because `AtomProvable` is opaque. Budget is
    irrelevant to truth. -/
axiom AtomProvable_sound : ∀ k φ, AtomProvable k φ → φ.interp


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

end PD.Axioms

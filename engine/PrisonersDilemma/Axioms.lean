import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PD
namespace PD.Axioms

/-!
# Axioms

The assumptions about the proof system `S` that are *not* discharged by the
explicit `Derivation` system. Each is a sound principle of a PA-like `S` that
the minimal model cannot witness constructively:

* `atom_complete`, `atom_monotone`, `AtomProvable_sound` — σ₁-completeness,
  budget-monotonicity, and soundness for atomic `.plays` facts;
* `box_provable` — bounded GL axiom 4 (HBL D2 / Solovay), currently unused;
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6);
* `Provable_transport_family` — CUPOD/DUPOC budget monotonicity (deferred; see
  below).

Everything else about `S` — soundness (`Derivation.sound`), the
`proofSearch ↔ Provable` bridge (`proofSearch_spec`), the source-transparency
steps (`proof_system_verifies_*`), and GL's K (`K_provable`) — is a *theorem*,
proved in `BaseTheorems.lean`.
-/

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

/--
**GL axiom 4 (`□φ → □□φ`), bounded form.** If `φ` is provable within budget `k`,
then *that fact* — `□_k φ` — is itself provable, at some larger budget `K`.

This is the Hilbert–Bernays–Löb derivability condition D2, and by Solovay's
theorem it is a genuine theorem of PA's provability logic — i.e. a sound
principle of any PA-like `S`. It is stated here, rather than derived, for two
reasons, both intrinsic to this minimal model (not to PA):

* the box is *budget-bounded*, so the conclusion needs a *larger* budget `K`
  than `k` (proving "there is a proof of size ≤ k" costs more than `k`
  characters) — hence the `∃ K`, mirroring `atom_complete`;
* its structural half *could* be a `Derivation` constructor (necessitation,
  `Derivation φ → Derivation (.box k φ)`), but a sound one needs the
  side-condition `(proof size) ≤ k`, unstatable in the constructor's type
  without size-indexing the whole `Derivation` type — unjustified for an unused
  principle. And the atomic half (where `φ`'s provability is the opaque
  `AtomProvable`, with no `Derivation` in hand) is irreducibly an assumption.

So its status matches `PBLT`/`atom_complete`: a true principle of `S` the
minimal model cannot witness constructively. It is consistent (its body is its
own soundness obligation, which is true) and currently unused. -/
axiom box_provable :
  ∀ (k : Nat) (φ : Formula), Provable k φ → ∃ K, Provable K (.box k φ)


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

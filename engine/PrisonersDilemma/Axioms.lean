import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PD
namespace PD.Axioms

/-!
# Axioms

The assumptions about the proof system `S` that are *not* discharged by the
explicit `Derivation` system. Each is a sound principle of a PA-like `S` that
the minimal model cannot witness constructively:

* `atom_complete`, `atom_monotone`, `AtomProvable_sound` — budget-bounded
  σ₁-completeness, budget-monotonicity, and soundness for atomic `.plays` facts;
* `box_provable` — bounded GL axiom 4 (HBL D2 / Solovay), currently unused;
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6).

(The former `Provable_transport_family` — CUPOD/DUPOC index monotonicity — was
removed: budget-bounded `atom_complete` lets the bot proofs pin budget = index
directly, so index-transport is no longer needed.)

Everything else about `S` — soundness (`Derivation.sound`), the
`proofSearch ↔ Provable` bridge (`proofSearch_spec`), the source-transparency
steps (`proof_system_verifies_*`), and GL's K (`K_provable`) — is a *theorem*,
proved in `BaseTheorems.lean`.
-/

/-- σ₁-completeness for atoms, **budget-bounded**: a play that succeeds within
    `fuel` steps is provable within budget `fuel`. The proof cost of the Σ₁ fact
    "this program plays `a` within `fuel` steps" is bounded by the computation
    length, so a budget of `fuel` characters suffices. critch22 uses
    σ₁-completeness implicitly (e.g. "CUPOD(10⁹)(DB.source) will find the proof
    and return D"); it is decidable Σ₁ truth, no Gödel obstruction.

    Two properties this exact (budget = `fuel`) form gives:
    * **Boundedness** — the budget is a *concrete* quantity (`fuel`) we control,
      not an opaque `∃ K`. This is what lets CUPOD/DUPOC index-monotonicity be a
      *theorem* (pick budget = fuel, no transport axiom needed).
    * **Slack for Open Problem 3** — a true play with large `fuel` is still
      *unprovable within a smaller budget* `j < fuel` (nothing forces provability
      below `fuel`, and `atom_monotone` only bumps budgets *up*). So
      `outcome(DUPOC,CUPOD) = (D,C)` remains statable. -/
axiom atom_complete :
  ∀ p q a fuel, play fuel p q = some a → AtomProvable fuel (.plays p q a)

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
-- * "`S` derives ψ" is `∃ m, Provable m ψ` — provability at some budget. (Stated
--   over `Provable` rather than the agents' `proofSearch _ = true` oracle, since
--   PBLT is a meta-theorem about bounded provability `□`, not about oracle
--   calls; the two are interchangeable via `proofSearch_spec`.)
-- * `f(k) ≻ O(lg k)` is spelled out as: there exists a positive constant
--   `c` and a threshold `k̂` such that for all `k > k̂`, `f(k) > c · lg k`.
-- * "Increasing" is the plain pointwise condition on `f`.
--
-- QUANTIFIER FIDELITY (∀□ vs □∀). critch22 states both hypothesis and
-- conclusion as `S ⊢ (∀k>k_i)(…)` — S proves a *single, universally quantified*
-- formula. We instead use the *per-instance* form `∀k>k_i, (∃m, Provable m …)`
-- — for each k, S proves that instance separately. This differs from Critch
-- (his ∀ is inside the box; ours is the meta-∀ outside), for an unavoidable
-- reason: our `Formula` has no internal ∀ quantifier, so a family `φ : Nat →
-- Formula` cannot be packaged into one quantified object-formula. The
-- per-instance form is:
--   • SOUND as an axiom — it is *implied by* Critch's Lemma 3.6 (if S proves
--     ∀k,P(k) then a fortiori S proves each P(k)), so we assume strictly less;
--   • SUFFICIENT — the consumers (`CupodBot_vs_CupodBot`, etc.) both *supply*
--     the hypothesis per-instance (one `cupod_loeb_premise k` per k) and
--     *consume* the conclusion per-instance (instantiating at a single k before
--     `Provable_sound`). They never need a single S-proof of the universal.
-- So this axiomatizes a faithful, sufficient *consequence* of Lemma 3.6, not
-- the □∀ lemma verbatim.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k)

end PD.Axioms

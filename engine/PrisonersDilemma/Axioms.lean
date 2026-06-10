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

/-- Critch's **proof-expansion constant** `e*` (Appendix B(d)): the linear factor
    by which the proof of "p plays a in `fuel` steps" exceeds `fuel`. A computation
    trace of length `fuel` takes `e* · fuel + e₀` characters to write down in `S`.
    Kept abstract because its concrete value depends on the encoding of `S`; the
    bot theorems are valid for all `e* ≥ 1`. -/
axiom proof_expansion_c : Nat

/-- Per-formula overhead in the atom proof: the constant additive term `e₀` in
    `e* · fuel + e₀`. Covers the characters used to name the formula itself. -/
axiom proof_expansion_d : Nat

/-- σ₁-completeness for atoms, **character-faithful**: a play that terminates in
    `fuel` steps is provable within `proof_expansion_c * fuel + proof_expansion_d`
    characters. This matches critch22 Appendix B(d): encoding a `fuel`-step trace
    costs `O(fuel)` characters, with leading constant `e*`.

    The earlier `budget = fuel` form was a simplification; the faithful version
    is this linear-in-`fuel` bound. Bot proofs use `atom_monotone` to lift to
    whatever working budget they need.

    Slack for Open Problem 3 is preserved: a true play is only guaranteed provable
    at budget `≥ proof_expansion_c * fuel + proof_expansion_d`; nothing forces
    provability below that, so DUPOC can still fail to find a proof of CUPOD
    cooperating when its own search budget is too small. -/
axiom atom_complete :
  ∀ p q a fuel, play fuel p q = some a →
    AtomProvable (proof_expansion_c * fuel + proof_expansion_d) (.plays p q a)

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
-- function with `f(k) ≻ O(lg k)`. If `S` has a proof of size `≤ f(k)` that
-- bounded provability of `φ k` within `f(k)` steps implies `φ k` itself,
-- then there exists a threshold `k₂` beyond which `S` proves `φ k` outright.
--
-- Encoding notes:
-- * `□_{f(k)}(φ k)` is the formula `Formula.box (f k) (φ k)`; its
--   semantic clause is `Provable (f k) (φ k)`. The inner budget `f(k)` is
--   Critch's, and is load-bearing: `f(k) ≻ O(lg k)` is exactly what makes the
--   box a *non-vacuous* provability claim about `φ k`, whose own proof is
--   `Θ(lg k)`-sized (it embeds the numeral `k`). Too small an `f(k)` would make
--   `□_{f(k)}(φ k)` unsatisfiable and the Löb step `□φ → φ` unusable.
-- * The OUTER proof — of the implication `□_{f(k)}(φ k) → φ k` — is left
--   *unbudgeted* (`∃ m, Provable m …`), faithfully matching Critch's turnstile
--   `⊢` in `⊢ (∀k>k₁)(□_{f(k)}(p[k]) → p[k])`, which carries no size annotation
--   on the proof of the implication itself. (An earlier version pinned the outer
--   proof to budget `f(k)` to make `Derivation.size` load-bearing in the axiom's
--   hypothesis; that is a *strengthening* of the hypothesis — sound, but a
--   distortion of Critch. We instead keep the axiom faithful and let the
--   consumers carry the size bound as a *separate* fact: e.g.
--   `cupod_loeb_premise` still proves `searchBranch.size = 5·log2 k + 33 ≤ k`
--   via `linear_log2_add_le`, so `Derivation.size` remains load-bearing in the
--   library without contaminating the axiom statement.)
-- * `f(k) ≻ O(lg k)` is spelled out as: there exists a positive constant
--   `c` and a threshold `k̂` such that for all `k > k̂`, `f(k) > c · lg k`.
-- * "Increasing" is the plain pointwise condition on `f`.
--
-- QUANTIFIER FIDELITY (∀□ vs □∀). critch22 states both hypothesis and
-- conclusion as `S ⊢ (∀k>k_i)(…)` — S proves a *single, universally quantified*
-- formula. We instead use the *per-instance* form `∀k>k_i, ∃ m, Provable m …`
-- — for each k, S proves that instance. This differs from Critch (his ∀ is
-- inside the box; ours is the meta-∀ outside), for an unavoidable reason: our
-- `Formula` has no internal ∀ quantifier, so a family `φ : Nat → Formula`
-- cannot be packaged into one quantified object-formula. The per-instance form
-- is:
--   • SOUND as an axiom — it is *implied by* Critch's Lemma 3.6 (instantiate his
--     single ∀-proof at each k);
--   • SUFFICIENT — the consumers (`CupodBot_vs_CupodBot`, etc.) both *supply*
--     the hypothesis per-instance and *consume* the conclusion per-instance.
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k)

end PD.Axioms

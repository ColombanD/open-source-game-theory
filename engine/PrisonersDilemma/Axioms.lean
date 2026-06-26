import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import Mathlib.Data.Nat.Log

open PD
namespace PD.Axioms

/-!
# Axioms

Principles of `S` not discharged constructively. Four remain (`c_guard_mono` is now
a theorem — the cost constants are concrete, see Derivation.lean; and
`atom_box_provable_impl` was REMOVED as unsound — see below). Each is interp-SOUND
(`box_provable` by HBL/Solovay; `boxInternalize` by `boxInternalize_sound` in
BaseTheorems.lean); they are axioms only for the *representational* reason that `Derivation`
has no box-introduction constructor and does not size-index proof trees, so a box-conclusion
/ box-antecedent witness cannot be built structurally.

* `atom_complete_false_guard` — the irreducible Π₁ residue: a play that branches
  on a *failed* guard has a certificate. Everything else is a theorem.
* `box_provable` — bounded GL axiom 4 (HBL D2), meta form. SOUND (provable-Σ₁-
  completeness on the genuinely-Σ₁ predicate `Provable k φ`).
* `boxInternalize` — box-internalization at a fixed budget `k`, between play-atoms (NOT GL
  axiom K — see its doc): from a budget-`k` proof transformer `Provable k φ → Provable k α`
  (α a play-atom), derive the object `□_k φ → □_k α`. SOUND via `boxInternalize_sound`: the
  conclusion's interp is *definitionally* the transformer itself (`:= hfitD`), so it is NOT
  false — it asserts nothing beyond its hypothesis. INERT for false atoms (no transformer
  exists, so e.g. DefectBot-cooperating stays unprovable). The fixed-budget form is FORCED:
  the faithful object-antecedent GL-K inflates the box budget and cannot be reconciled to the
  `k` that PBLT + the opponent leg demand (machine-confirmed dead end,
  `Research/Spikes/HonestKSpike.lean`; cf. `MutualLobSpike.lean`). `boxInternalize` + the two
  transparency legs derive the cross-bot Löb premise as the THEOREM `mutual_loeb`
  (BaseTheorems.lean), closing the fixpoints (PrudentBot↔DupocBot, three guises) the removed
  unsound `atom_box_provable_impl` formerly forced.
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6).

Everything else is a theorem in `BaseTheorems.lean`.
-/


/-- The Π₁ residue of σ₁-completeness: a play that has no constructive `PlaysProof`
    certificate (because it branched on a *failed* proof search, requiring
    `¬ Provable k (guard)` — Π₁, non-positive) still has an `AtomProvable` certificate
    at budget `atom_cost fuel`. Use `atom_complete` (the theorem below) at call sites.

    STATUS — LOAD-BEARING and DECIDABLE-but-uncarried (corrected 2026-06-26).

    * **It IS load-bearing.** An earlier note here claimed "no theorem's truth depends
      on it." That was WRONG: a call-site survey found ≈5 genuine false-guard plays that
      route through this axiom — a `.search`-bot playing its *else*-branch action, e.g.
      `PrudentBot plays D vs .bot DefectBot` (`prudence_self_prudent`,
      `Theorems/LlmGenerations/PrudentBot.lean`), `JustBot plays D vs .bot DefectBot`,
      `CupodTrollBot plays C vs DupocBot`. These feed real cross-bot outcome theorems.

    * **Its content is DECIDABLE, not witness-free.** The fact "no size-≤-k `PlaysProof`
      of the guard exists" is the negation of a DECIDABLE predicate: the sound, computable
      checker `ppSize` (`ComputableEval/PlaysCheck.lean`, `ppSize_sound`) decides bounded
      play-certificate existence by a terminating procedure. So this axiom postulates a
      decidable fact, not an oracle. The eval-trace bridge `eval_search_false` (same file)
      connects a failed guard to the real else-branch play.

    * **Why it stays an axiom — TWO walls, both now machine-located.**

      WALL 1 (positivity, lifted). A `search_f` constructor carrying `¬ Provable`/`¬ PlaysProof`
      is kernel-impossible (non-positive). This IS liftable: `Provable_fin` (`Derivation.lean`,
      a decidable `proofSearch`-free finite-provability predicate) is now defined BEFORE the
      `PlaysProof`/`Provable` mutual block (the cycle-break), so a `search_f` carrying
      `decide (Provable_fin k guard) = false` is kernel-POSITIVE and TYPECHECKS. We verified
      this in-engine (`ProvableFinSpike.lean`, and a transient real-engine `search_f`).

      WALL 2 (soundness, NOT lifted — the deeper boundary). Even typeable, `search_f` is NOT
      SOUND. `playsProof_sound` must discharge it for EVERY `search_f` certificate, and that
      needs `proofSearch k guard = false` (eval-exact: `eval` runs the else-body only when the
      guard fails). But `decide (Provable_fin k guard) = false` does NOT imply `proofSearch k
      guard = false`: at a Löb fixpoint `Provable_fin = false` while `Provable`/`proofSearch`
      is `PBLT`-axiom-TRUE. And `eval` CANNOT be rewired to consult `Provable_fin` instead of
      `proofSearch` — the PBLT cooperations (e.g. `CupodBot.lean:112`) REQUIRE `proofSearch =
      true` at the self-referential fixpoint guard, where `Provable_fin` is false. So the
      sound premise is the Π₁ fact `¬ Provable k guard`, irreducibly non-positive in-block.

      Net: the cycle-break makes the false-guard fact DECIDABLE and the constructor TYPEABLE,
      but the Löb fixpoint forces the SOUNDNESS premise to be the non-positive Π₁ negation.
      The two coincide (`Provable_fin = false ↔ proofSearch = false`) exactly OFF the fixpoints
      — which is the same proof-vs-witness boundary as the noncomputable-`eval` crux. Removing
      this axiom is entangled with `PBLT` (the Löb axiom) and is NOT independently dischargeable.

    Machine-grounded investigation: `Research/Spikes/{SearchFFeasibilitySpike,SizeIndexSpike,
    PortPhaseASpike,DecidableFiniteSpike,ProvableFinSpike}.lean`. `Provable_fin` /
    `instDecProvableFin` / `provableFin_sound` / `ppSize` (the computable, sound decider) are
    shipped IN-ENGINE (`Derivation.lean`, `ComputableEval/PlaysCheck.lean`): the false-guard
    fact's existence is decidable; only its SOUND in-`PlaysProof` carriage is blocked, by the
    Π₁/PBLT entanglement above. -/
axiom atom_complete_false_guard :
  ∀ p q a fuel, play fuel p q = some a →
    ¬ (∃ _ : PlaysProof p q p a (atom_cost fuel), True) →
    AtomProvable (atom_cost fuel) (.plays p q a)

/-- Bounded GL axiom 4 (`□_k φ → □_K □_k φ`): if `φ` is provable within budget
    `k`, then that fact is itself provable at a budget `K` **bounded by the size of
    the boxed formula** `□_k φ`. Sound by Solovay / HBL D2; axiomatic here because the
    budget-indexed box makes a constructive witness impossible without size-indexing
    `Derivation`. The `K ≤ (.box k φ).size` bound (honest bounded-GL-4) is what lets
    the consumer `atom_box_provable_impl_sound` feed `K` into the now budget-bounded
    `weakenImpl` (`m ≤ k`): the boxed atom's size is sub-`k` whenever the implication
    fits `k`. -/
axiom box_provable :
  ∀ (k : Nat) (φ : Formula), Provable k φ →
    ∃ K, K ≤ (Formula.box k φ).size ∧ Provable K (.box k φ)

/-- **Box-internalization at a fixed budget `k`** (NOT GL axiom K — see below).

    Given a budget-`k` *proof transformer* `hfitD : Provable k φ → Provable k α` for a
    play-atom `α = .plays p q c`, internalize it as the object box implication
    `□_k φ → □_k α` at budget `k` (size permitting).

    **WHY THIS IS SOUND, AND NOT FALSE.** Its `interp` is, definitionally,
    `Provable k φ → Provable k α` — i.e. *exactly its own hypothesis* `hfitD`. So the axiom
    asserts nothing beyond what the caller already holds: `boxK_sound` is literally `:= hfitD`,
    a tautology, and depends only on the Lean-standard axioms. It is INERT where it could do
    harm: to fire it you must SUPPLY `hfitD`, and for a false atom (e.g. `DefectBot plays C`,
    interp-false) no such transformer exists, so nothing false becomes provable.

    **WHY IT IS NOT GL AXIOM K (honest naming).** Real K is `⊢ □_a(φ→ψ) → (□_aφ → □_aψ)`,
    with an *object* antecedent `□_a(φ→ψ)`. Here the antecedent is a *meta-level* Lean
    proof-transformer, and the conclusion's box stays at `k` (no necessitation cost paid).
    This is a budget-aligned *internalization* rule, not K. The faithful object-antecedent K
    is a DEAD END for this proof: it is sound only with an EXISTENTIAL output box budget (the
    re-derived atom's certificate cost), which cannot be reconciled to the `k` that `PBLT` and
    the opponent leg `legDP` both demand — bridging `□_{cert} α → □_k α` would need box-INDEX
    weakening, which is genuinely unsound. Machine-confirmed in `Research/Spikes/HonestKSpike.lean`
    (and the budget non-composition of separate K/4/necessitation in `MutualLobSpike.lean`).
    The fixed-`k` is FORCED, not a shortcut: the bot searches at its own budget `k`
    (`CONSTRUCTIVE_BOUNDED_LOB.md` S3′), so the true content `Provable k φ → Provable k α`
    lives at `k`, and internalizing it at `k` is the only sound, semantics-matching form. -/
axiom boxInternalize :
  ∀ (k : Nat) (φ : Formula) (p q : Prog) (c : Action),
    (Provable k φ → Provable k (.plays p q c)) →
    (Formula.impl (.box k φ) (.box k (.plays p q c))).size ≤ k →
    Provable k (.impl (.box k φ) (.box k (.plays p q c)))

/-! ### REMOVED — `atom_box_provable_impl` (was unsound)

    Formerly an axiom asserting the *witness-free* object implication
    `⊢ (p plays a vs q) → □_k (p plays a vs q)` for ALL `k p q a`, with no
    threshold. It was **unsound in the `interp` model**: applied through
    `Provable_sound`, its interp is `(∃n, play n p q = a) → Provable k (.plays p q a)`,
    which forces a size-≤-`k` certificate to exist whenever the play merely happens
    at SOME fuel — false for any play whose certificate exceeds `k` (`atom_cost fuel
    > k`). Now exhibitable since the cost model (`c_guard`, `atom_cost`) is concrete.

    The SOUND content it gestured at survives in two places, neither witness-free:
    * `BaseTheorems.atom_box_provable_impl_sound` — the conditional THEOREM carrying
      the threshold `atom_cost fuel ≤ k` (genuine bounded Σ₁-completeness); and
    * `Provable.atomBoxImpl` (Derivation.lean) — its constructive, certificate-carrying
      realization as a `Provable` rule, discharged with NO axiom.

    The matchups that USED the unsound form — `outcome_PrudentBot_vs_DupocBot`,
    `llm_outcome_JustBot_vs_PrudentBot`, `llm_outcome_JustBot_vs_DupocBot` — are
    genuine Löb fixed points whose box-introduction on the (as-yet-unproven) cooperative
    atom needs reflection beyond a single bot's transparency. They are now CLOSED (no
    `sorry`) by the SOUND `boxInternalize` axiom above (mutual Löb): rather than boxing a
    bare atom, the `mutual_loeb` theorem feeds `boxInternalize` a budget-`k` proof transformer
    `Provable k φP → Provable k φD` — obtained from BOTH bots' transparency legs via a guard
    inversion that fires only at a genuine two-bot fixpoint — so nothing false (e.g.
    DefectBot cooperating) becomes provable. See
    `mutual_loeb`/`mutual_loeb_sound`/`boxInternalize_sound` (BaseTheorems.lean) and
    `Research/Spikes/MutualLobSpike.lean`. -/

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

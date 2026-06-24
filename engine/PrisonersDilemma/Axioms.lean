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
(`box_provable` by HBL/Solovay; `boxK` by `boxK_sound` in BaseTheorems.lean); they are
axioms only for the *representational* reason that `Derivation` has no box-introduction
constructor and does not size-index proof trees, so a box-conclusion / box-antecedent
witness cannot be built structurally.

* `atom_complete_false_guard` — the irreducible Π₁ residue: a play that branches
  on a *failed* guard has a certificate. Everything else is a theorem.
* `box_provable` — bounded GL axiom 4 (HBL D2), meta form. SOUND (provable-Σ₁-
  completeness on the genuinely-Σ₁ predicate `Provable k φ`).
* `boxK` — bounded GL axiom K (`□` distributes over `→`) at a single fixed budget `k`,
  between play-atoms: from a budget-`k` proof transformer `Provable k φ → Provable k α`
  (α a play-atom), derive the object `□_k φ → □_k α`. SOUND via `boxK_sound` (interp is the
  transformer itself, tautological). The single-fixed-budget form is forced: separate
  K/4/necessitation each pick their own existential box budget and cannot be re-aligned to
  `k`, so they do NOT compose into the cross-bot Löb premise (machine-confirmed,
  `Research/Spikes/MutualLobSpike.lean`). `boxK` + the two transparency legs derive that
  premise as the THEOREM `mutual_loeb` (BaseTheorems.lean). NON-collapsible: the caller can
  only supply the proof transformer via a guard inversion that fires at a genuine two-bot
  fixpoint, so nothing false (e.g. DefectBot cooperating) becomes provable. This closes the
  cross-bot fixpoints (PrudentBot↔DupocBot, in three guises) the removed unsound
  `atom_box_provable_impl` formerly forced.
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6).

Everything else is a theorem in `BaseTheorems.lean`.
-/


/-- The irreducible Π₁ residue of σ₁-completeness: a play that has no
    constructive `PlaysProof` certificate (because it branched on a *failed*
    proof search, requiring `¬ Provable k (guard)` — Π₁, non-positive) still
    has an `AtomProvable` certificate at budget `atom_cost fuel`.
    Use `atom_complete` (the theorem below) at call sites.

    NOTE — currently not *force-exercised* by the library. `atom_complete` is the
    only consumer, via a `by_cases` on whether a constructive `PlaysProof` exists;
    every call site to date (CupodBot/DupocBot/CupodTrollBot theorems) transcribes
    a play whose internal guards all fire *true* (or has no guard at all — const
    bots), so it always lands in the constructive branch and this axiom is never
    forced. It is referenced (so it compiles) but no theorem's truth yet depends
    on it.

    To genuinely exercise it you need to lift a *failed-guard cooperation* into a
    provable atom — i.e. some bot `Z` that proof-searches "does my opponent
    cooperate with me?" (`.search k (.plays .opp .self .C) …`) played against
    CUPOD. CUPOD cooperates with `Z` by taking its *else* (failed-guard) branch,
    so certifying `.plays (CupodBot k) Z .C` needs the missing `search_f` step —
    no constructive `PlaysProof` exists, and `atom_complete` falls through here.
    No such bot is in the library yet; add one (e.g. a "CupodProber") to make this
    axiom load-bearing, or drop it and restrict `atom_complete` to the true-guard
    / const fragment the library actually uses. -/
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

/-- **Bounded GL axiom K**, at a single fixed budget `k`, between play-atoms.

    The standard modal axiom K — `□` distributes over `→` — specialized to the
    budget-aligned form the cross-bot Löb premise actually needs: given a *proof transformer*
    `hfitD : Provable k φ → Provable k α` (the bounded-`k` content of `⊢ □_k(φ→α)`,
    necessitation already applied) for a play-atom `α = .plays p q c`, the object box
    implication `□_k φ → □_k α` is provable **at the same budget `k`** (size permitting).

    Why this single fixed-`k` form (and not separate K/4/necessitation): each of those picks
    its own existential box budget and they cannot be re-aligned to `k`, so they do not
    compose into the conclusion (machine-confirmed; see `mutual_loeb` and
    `Research/Spikes/MutualLobSpike.lean`). Keeping K's input and output box both at `k`,
    with the proof-transformer premise carrying the budget, is the GL-K content that closes.

    SOUND (`boxK_sound`): `interp (□_k φ → □_k α)` is `Provable k φ → Provable k α`, which is
    `hfitD` itself — tautological. The play-atom restriction on `α` is what makes a caller
    able to SUPPLY `hfitD` honestly (via a guard inversion landing at budget `k`), NOT a
    soundness condition on K. Standard, named, single-budget. -/
axiom boxK :
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
    `sorry`) by the SOUND, standard GL axiom `boxK` above (mutual Löb): rather than boxing
    a bare atom, the `mutual_loeb` theorem feeds `boxK` a budget-`k` proof transformer
    `Provable k φP → Provable k φD` — obtained from BOTH bots' transparency legs via a guard
    inversion that fires only at a genuine two-bot fixpoint — so nothing false (e.g.
    DefectBot cooperating) becomes provable. See `mutual_loeb`/`mutual_loeb_sound`/`boxK_sound`
    (BaseTheorems.lean) and `Research/Spikes/MutualLobSpike.lean`. -/

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

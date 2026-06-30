import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import Mathlib.Data.Nat.Log

open PD
namespace PD.Axioms

/-!
# Axioms

Principles of `S` not discharged constructively. **TWO remain** (down from four):

* `atom_complete_false_guard` — the irreducible Π₁ residue: a play that branches on a *failed*
  guard still has an `AtomProvable` certificate. Proven irreducible — the else-action has no
  certificate TERM at all (`ComputableEval/Exclusion.lean`), so the axiom postulates a true
  `interp` whose witness provably does not exist (the proof-vs-witness gap).
* `PBLT` — the Parametric Bounded Löb Theorem (critch22 Lemma 3.6). A genuine metatheorem
  (bounded-Löb / diagonalization), removable only by a faithful first-order mechanization of `S`
  (`Bew` + a deduction theorem); see `Research/Notes/EXPLICIT_S_PROPOSAL.md`. Critch's proof is
  in `PBLT_proof.tex` §5.

Removed (now theorems / constructors, NO new axioms; `Provable_sound` still rests on only the 3
Lean-standard axioms):

* `box_provable` (bounded GL-4 necessitation) → the `Provable.boxIntro` constructor + the
  `BaseTheorems.box_provable` theorem.
* `boxInternalize` (box-internalization at the cross-bot Löb fixpoints) → the `app`/`axK`/`box4`
  constructors; `mutual_loeb` (BaseTheorems.lean) builds the closed Löb premise from the two object
  transparency legs (Route 2). The faithful object-antecedent GL-K was a dead end
  (`Research/Spikes/bounded_lob/HonestKSpike.lean`); the working route uses a proof-TERM premise.
* `atom_box_provable_impl` — removed as unsound; sound content survives as
  `atom_box_provable_impl_sound` (theorem) + the `atomBoxImpl` constructor.
* `c_guard_mono` — now a theorem (the cost constants are concrete, see Derivation.lean).

Everything else is a theorem in `BaseTheorems.lean`.
-/


/-- **The Π₁ residue of σ₁-completeness.** A play that has no constructive `PlaysProof` certificate
    (it branched on a *failed* proof search, requiring `¬ Provable k guard` — Π₁, non-positive) still
    has an `AtomProvable` certificate at budget `atom_cost fuel`. Use `atom_complete` (theorem below)
    at call sites.

    **Load-bearing.** ≈5 false-guard plays route through this axiom — a `.search`-bot playing its
    *else*-action, e.g. `PrudentBot plays D vs .bot DefectBot` (`prudence_self_prudent`), `JustBot
    plays D vs .bot DefectBot`, `CupodTrollBot plays C vs DupocBot` — feeding real cross-bot outcomes.

    **Decidable, not witness-free.** "No size-≤-k `PlaysProof` of the guard exists" is the negation
    of a DECIDABLE predicate (`ppSize` / `Provable_fin`, `ComputableEval/PlaysCheck.lean`, computes
    it soundly). The axiom postulates a decidable fact, not an oracle.

    **Irreducible — two walls.** A `search_f` constructor producing the else-action would discharge
    it, but: (WALL 1, positivity — liftable) `¬ Provable` is non-positive in-block, but a
    `decide (Provable_fin k guard) = false` premise typechecks via the `Provable_fin` cycle-break;
    (WALL 2, soundness — NOT liftable) `Provable_fin = false ⇏ proofSearch = false` at a Löb fixpoint
    (`Provable_fin` false while `proofSearch`/`Provable` is `PBLT`-axiom-true), and `eval` can't be
    rewired to `Provable_fin` (the PBLT cooperations need `proofSearch = true` at the fixpoint). So
    the sound premise is the non-positive Π₁ `¬ Provable k guard`. Deepest: the else-play's
    certificate type is provably EMPTY — no `Derivation`/`PlaysProof`/`Provable` concludes it
    (`ComputableEval/Exclusion.lean`, `[propext]`). So the axiom postulates a true `interp` whose
    proof TERM does not exist (the proof-vs-witness gap), entangled with `PBLT` off-fixpoints.

    Spikes: `Research/Spikes/atom_complete_false_guard/`. -/
axiom atom_complete_false_guard :
  ∀ p q a fuel, play fuel p q = some a →
    ¬ (∃ _ : PlaysProof p q p a (atom_cost fuel), True) →
    AtomProvable (atom_cost fuel) (.plays p q a)

-- (The removed axioms `box_provable`, `boxInternalize`, `atom_box_provable_impl`, `c_guard_mono` and
--  where their content now lives are summarized in the module header above. The two live axioms
--  follow.)

/-- **Parametric Bounded Löb Theorem** (critch22 Lemma 3.6). If `f(k) ≻ O(log k)` and `S` proves
    `□_{f(k)} φ(k) → φ(k)` for all large `k`, then `S` proves `φ(k)` outright for all large `k`.

    A genuine metatheorem (bounded Löb / diagonalization), not a representational wall — removable
    only by a faithful first-order mechanization of `S` (Gödel `Bew` + a deduction theorem), which
    `Provable`'s deliberately bounded, deduction-free design does not support. See
    `Research/Notes/EXPLICIT_S_PROPOSAL.md` (the `BPS` interface spike) and `PBLT_proof.tex` §5.

    Shape notes:
    * The hypothesis's proof budget is *unbudgeted* (`∃ m, Provable m …`) — faithful to Critch's
      `⊢`, which carries no size annotation on the implication proof. Consumers (CupodBot, DupocBot)
      supply the `f(k) ≻ O(log k)` bound via `linear_log2_add_le` + `Derivation.size`.
    * We use a per-instance meta-`∀ k` (`∀ k > k₁, ∃ m, …`) rather than Critch's single
      universally-quantified object-formula, because `Formula` has no internal `∀` quantifier. This
      is implied by Critch's statement and sufficient for all consumers. -/
axiom PBLT :
  ∀ (φ : Nat → Formula) (f : Nat → Nat) (k₁ : Nat),
    (∀ a b, a ≤ b → f a ≤ f b) →
    (∃ c kHat, c > 0 ∧ ∀ k, k > kHat → f k > c * Nat.log2 k) →
    (∀ k, k > k₁ → ∃ m, Provable m (.impl (.box (f k) (φ k)) (φ k))) →
      ∃ k₂, ∀ k, k > k₂ → ∃ m, Provable m (φ k)

end PD.Axioms

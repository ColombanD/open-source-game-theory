import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import Mathlib.Data.Nat.Log

open PD
namespace PD.Axioms

/-!
# Axioms

Principles of `S` not discharged constructively. **ONE remains** (down from four):

* `atom_complete_false_guard` — the irreducible Π₁ residue: a play that branches on a *failed*
  guard still has an `AtomProvable` certificate. Proven irreducible — the else-action has no
  certificate TERM at all (`ComputableEval/Exclusion.lean`), so the axiom postulates a true
  `interp` whose witness provably does not exist (the proof-vs-witness gap).

Removed 2026-07-01: `PBLT` — now a THEOREM (`BaseTheorems.bloeb_engine`/`pblt_engine`), proven
inside `Provable` via the internalized Löb-fixpoint sentence `Formula.diag` and the
`diagF`/`diagB`/`axKf`/`impS2` rules; see the note at the end of this file.

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
    (WALL 2, soundness — NOT liftable) `Provable_fin = false ⇏ proofSearch = false` at a Löb fixpoint:
    `Provable_fin` (the `PlaysProof`-fragment decider) is false there while `proofSearch`/`Provable`
    is TRUE — the fixpoint cooperations are DERIVED (since 2026-07-01 via `bloeb_engine`'s `.diag`
    route, real constructor trees rather than the former `PBLT` axiom, but still not `PlaysProof`
    certificates) — and `eval` can't be rewired to `Provable_fin` (the Löb cooperations need
    `proofSearch = true` at the fixpoint). So the sound premise is the non-positive Π₁
    `¬ Provable k guard`. Deepest: the else-play's certificate type is provably EMPTY — no
    `Derivation`/`PlaysProof`/`Provable` concludes it (`ComputableEval/Exclusion.lean`, `[propext]`;
    the exclusion recs cover the `.diag` rules too). So the axiom postulates a true `interp` whose
    proof TERM does not exist (the proof-vs-witness gap), entangled with the Löb fixpoints.

    Spikes: `Research/Spikes/atom_complete_false_guard/`.

    ⚠️⚠️ **INCONSISTENT — machine-checked (2026-07-02).** The anti-diagonal bot
    `G := .search 100 (.plays .self .self .D) (.const .C) (.const .D)` refutes this axiom:
    its else-certificate is injected at `atom_cost 2 = 7`, which `atom_monotone` lifts back
    above the guard budget it refutes, flipping the guard — both guard values yield `False`
    (`Research/Spikes/transcript/T32Inconsistency.lean`, `engine_inconsistent : False`).
    Every result whose `#print axioms` lists this axiom is VACUOUS until it is repaired.
    Root cause: the injection budget depends only on FUEL and can sit below the refuted
    guard's own search budget. Repair direction (DECIDABILITY_ROADMAP.md T3.2): the CHARGED
    atom model — else-certificates must exceed the guard budget they refute. -/
axiom atom_complete_false_guard :
  ∀ p q a fuel, play fuel p q = some a →
    ¬ (∃ _ : PlaysProof p q p a (atom_cost fuel), True) →
    AtomProvable (atom_cost fuel) (.plays p q a)

-- (The removed axioms `box_provable`, `boxInternalize`, `atom_box_provable_impl`, `c_guard_mono` and
--  where their content now lives are summarized in the module header above. The two live axioms
--  follow.)

/- **`PBLT` — DELETED (2026-07-01): now a THEOREM.** The Parametric Bounded Löb Theorem
   (critch22 Lemma 3.6) is PROVEN inside `Provable` itself — see `BaseTheorems.bloeb_engine`
   (Löb's chain at one subscript-and-budget, from the tight premise, via the `.diag` fixpoint
   sentence and the `diagF`/`diagB`/`axKf`/`impS2` rules) and `BaseTheorems.pblt_engine` /
   `pblt_engine_id` (the `∃k₂, ∀k>k₂, ∃m, Provable m (φ k)` conclusion the consumers use).
   `#print axioms pblt_engine` = {propext, Quot.sound} — no axiom beyond Lean's standard ones.

   The internalization: `Formula.diag g tgt` is the Löb-fixpoint sentence (its `interp` IS the
   fixpoint, Dynamics.lean — same design pattern as `.box n φ ↦ Provable n φ`); the diagonal
   rules are Löb-premise-gated sound constructors. Meta-justification (that a faithful
   arithmetization contains such a sentence): the Reflection layer's DERIVED diagonal
   (`Reflection/Proves.lean` `repr_object` over the predicate-level `selfApply`). Design +
   validation: `Research/Notes/INTERNALIZATION_ROADMAP.md`, `Research/Spikes/pblt/I0Design.lean`.

   The former axiom's signature differences (both strictly-weaker hypotheses were never used):
   * it took a LOOSE premise `∃ m, Provable m (…)` — the theorem takes the TIGHT
     `Provable (f k) (…)`, which is what every consumer's `*_loeb_premise` lemma produces;
   * it carried monotonicity/log-domination hypotheses on `f` — the theorem takes the one bound
     it actually needs (`9·log2(f k) + 6·(φ k).size + 32 ≤ f k`, eventual). -/

end PD.Axioms

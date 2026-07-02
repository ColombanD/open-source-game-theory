import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import Mathlib.Data.Nat.Log

open PD
namespace PD.Axioms

/-!
# Axioms — **ZERO remain** (2026-07-02).

`atom_complete_false_guard`, the last project axiom, is DELETED — it was **INCONSISTENT**
(machine-checked `False`: the anti-diagonal bot `G := .search 100 (.plays .self .self .D)
(.const .C) (.const .D)` — its else-certificate was injected at `atom_cost 2 = 7`, which
`atom_monotone` lifted back above the guard budget it refutes, flipping the guard; both guard
values yield `False`. `Research/Spikes/transcript/T32Inconsistency.lean`, now stated
hypothesis-relative). The zoo never built anti-diagonal guards, which is why every outcome
theorem still type-checked; the results that cited the axiom were vacuous.

**The sound replacement** (2026-07-02, the false-guard repair):
* `PlaysProof.search_f` — the else-branch certificate, premised on a REFUTATION of the guard
  (`Provable m (.neg guard)`, Σ₁) and paying the FULL failed budget `k` (the floor — an
  else-certificate must never fit within the budget whose failure it certifies);
* `Provable.atomNeg` — refutations of play-atoms from certificates of the actual play
  (eval determinism);
* `BaseTheorems.atom_complete_searchfree` / `atom_search_t_top` / `atom_search_f_top` (and
  `_bot_top` variants) — the constructive certificate toolkit replacing the deleted
  `atom_complete`. For guards that are false but IRREFUTABLE (the anti-diagonal's own), the
  else-play is TRUE BUT UNCERTIFIABLE — the honest Gödelian boundary, no axiom papering it.

Consequently some previously-"proved" outcomes were axiom artifacts and are now honestly
restated or retired (staggered budgets — Critch-faithful; see DECIDABILITY_ROADMAP.md T3.2a).

Removed 2026-07-01: `PBLT` — now a THEOREM (`BaseTheorems.bloeb_engine`/`pblt_engine`), proven
inside `Provable` via the internalized Löb-fixpoint sentence `Formula.diag` and the
`diagF`/`diagB`/`axKf`/`impS2` rules; see the note at the end of this file.

Removed earlier (now theorems / constructors):

* `box_provable` (bounded GL-4 necessitation) → the `Provable.boxIntro` constructor + the
  `BaseTheorems.box_provable` theorem.
* `boxInternalize` (box-internalization at the cross-bot Löb fixpoints) → the `app`/`axK`/`box4`
  constructors; `mutual_loeb` (BaseTheorems.lean) builds the closed Löb premise from the two object
  transparency legs (Route 2). The faithful object-antecedent GL-K was a dead end
  (`Research/Spikes/bounded_lob/HonestKSpike.lean`); the working route uses a proof-TERM premise.
* `atom_box_provable_impl` — removed as unsound; sound content survives as
  `atom_box_provable_impl_sound` (theorem) + the `atomBoxImpl` constructor.
* `c_guard_mono` — now a theorem (the cost constants are concrete, see Derivation.lean).

This module is kept as the historical record; it declares NOTHING. Every principle of `S` is a
constructor or a theorem, and the whole engine rests on Lean's three standard axioms.
-/

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

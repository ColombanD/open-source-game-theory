---
name: project_pblt_removal_plan
description: "PBLT AXIOM DELETED (2026-07-01, branch colomban-proving-lob) — bounded Löb PROVEN inside Provable via internalization (.diag fixpoint + 4 rules). Engine at ONE axiom (atom_complete_false_guard). How it was done + what NOT to retry."
metadata:
  node_type: memory
  type: project
  originSessionId: 45e03dc3-6b3d-4188-b97e-57f9c3c1ed30
---

**DONE (2026-07-01): the `PBLT` axiom is DELETED. Bounded Löb is a THEOREM of the engine.**
Engine axiom count 4 → 1 (`atom_complete_false_guard` remains — machine-proven irreducible, the
Π₁ false-guard residue; it is the honest floor).

**How (the internalization, milestones I0–I5; `Research/Notes/INTERNALIZATION_ROADMAP.md`):**
- `Formula.diag (g : Nat) (tgt : Formula)` — the Löb-fixpoint sentence; its `interp` IS the fixpoint
  BY DEFINITION: `Provable g (.diag g tgt) → tgt.interp` (legal: recursion only into tgt; same design
  pattern as `.box n φ ↦ Provable n φ`). subst FROZEN; size like `.box`.
- FOUR `Provable` rules: `diagF`/`diagB` (fixpoint legs, sound = identity, GATED on the tight Löb
  premise — the gate is what keeps the CIMCIC/DIMCID/Exclusion structural-exclusion recs provable),
  `axKf` (object-FORMULA K, sound = app; rule-form axK provably insufficient for Löb's middle step),
  `impS2` (closed composition, replaces the deduction theorem).
- `BaseTheorems.bloeb_engine` — Löb's chain at ONE subscript-and-budget u from the TIGHT premise
  `Provable u (□_u φ → φ)`: **NO axioms at all**. `pblt_engine` (∃k₂ conclusion): {propext, Quot.sound}.
  `pblt_engine_id` — consumer wrapper (uniform `10·log2 k + 100` size bound covers the whole zoo).
- All 12 former call sites (DupocBot ×2, CupodBot ×2, PrudentBot ×5, JustBot ×3) repointed: each
  already HELD the tight premise via its `*_loeb_premise` lemma (the ∃m-loosening was only to feed the
  axiom); dead hMono/hLog blocks removed.
- SWEEP: DupocBot/CupodBot outcomes now on the 3 Lean-standard axioms ONLY; PrudentBot/JustBot on
  3 std + atom_complete_false_guard (as always, for their false-guard else-plays).

**Key design facts (for future work):**
- Engine cost model (proof cost = CONCLUSION character size) kills Critch's `E`-expansion entirely;
  everything runs at u = f k; the ~13 size side-conditions are `O(log k)`-shaped, discharged by
  `simp [Formula.size]; omega` from `linear_log2_add_le`.
- The tight-premise form is what consumers produce; the old axiom's ∃m-loose + monotone/log-domination
  hypotheses were never actually used.
- Meta-justification of `.diag` (that a faithful arithmetization contains the fixpoint sentence): the
  Reflection layer's DERIVED diagonal (`repr_object` over the predicate-level `selfApply θ := betaA θ`,
  spike B4). The Reflection/ layer is now historical/meta-justification, not load-bearing.
- Validated end-to-end FIRST in `Research/Spikes/pblt/I0Design.lean` (mini-engine, engine-exact
  signatures; `bloeb_mini` no-axioms) — the transplant then compiled first try.

**What this does NOT give (do not conflate):** computable `eval` (route B). `proofSearch` remains
classical/noncomputable; decidability of the enriched `Provable` is a separate open question (the
mp-cut/enumeration wall, machine-checked in MN1_decidable.lean). See
[[project_computable_eval_routeii]], [[project_pblt_vs_constructive_lob]].

**Do NOT retry (settled negatives from the route to here):** side-layer BWD extraction
(`provesN_play_extract` — unstateable back-translation / mp-cut), model/realizability extraction
(unsound, ConstructiveLobToy §8), decidable-box enumeration (atom-closure false), classical case-split
at fixpoints (Löb knot). The internalization was the correct and only route.

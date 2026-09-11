---
name: project_pblt_vs_constructive_lob
description: "Critch's PBLT (faithful, classical, existential) ≠ constructive bounded Löb (computable eval). Two different theorems for two different goals. Design note written 2026-06-23."
metadata: 
  node_type: memory
  type: project
  originSessionId: 4772936d-34f0-495d-bcc0-0af81873e600
---

Established 2026-06-23 while scoping "prove PBLT in Lean". The PBLT proof is in
`PBLT_proof.tex` (Critch §5, complete + correct, no gaps).

**The core distinction (do not conflate):**
- **(A) Critch's PBLT** — faithful mechanization. Goal: "explicit S" / honest axiom
  surface. NON-constructive (classical diagonal lemma → `∃m, Provable m φ`, no extractable
  witness). Does **NOT** make `eval` computable.
- **(B) Constructive bounded Löb** — THE crux lever for computable `eval`. Builds a
  size-≤-k proof TERM. Constructive. A theorem **Critch did NOT prove** (his formal PBLT
  discards the constructive content the informal FairBot argument gestures at).

Colomban chose to pursue **(B)**.

**Why (A)≠(B) matters:** transcribing Critch faithfully (abstract-interface OR full
Gödel-encoded) leaves eval noncomputable. Abstract-interface just moves the IOU from one
`PBLT` axiom into 4–5 witness-free structure fields (Critch Properties 4.1–4.4 + Parametric
Diagonal Lemma) — still existential, still non-decidable.

**Mathlib for full-faithful (A):** only the scaffolding floor (`ModelTheory` syntax/
semantics/encoding ~15-20%). NO `Bew`, no arithmetized provability, no incompleteness, no
derivability conditions D1–D3, nothing BOUNDED. Bounded GL exists in NO Lean library. The
hard core is built from zero. (Lean Gödel-I lives in external repos, not Mathlib; Paulson's
is Isabelle.)

**(B)'s wall:** the FairBot↔FairBot / CUPOD↔CUPOD fixpoint certificate needs itself as a
`search_t` premise → forbidden by `PlaysProof` being a LEAST fixed point (correctly).

**SPIKE RESULTS (2026-06-23, `Research/Spikes/BoundedLobSpike.lean`, not imported by root):**
- **S1 PASSED:** the `boundedLob` combinator (strong recursion on budget k) is well-formed
  in Lean — total, well-founded. The machinery exists. (Caveat: WF recursion doesn't reduce
  by rfl, unfold via `boundedLob.eq_def`.)
- **S3 FAILED (as a design):** the combinator does NOT fit the real CUPOD discharge. The
  engine's `cupod_loeb_premise` gives `□_k φ → φ` whose interp (`Provable_sound`) is
  `Provable k φ → φ.interp` — antecedent and conclusion at the SAME budget k, and antecedent
  is a PROOF while conclusion is a PLAY. So (1) predicate mismatch (can't feed output back),
  (2) budget mismatch (no smaller-budget premise to recurse on; c_guard decrease lives
  INSIDE the cert, not in the antecedent box). Naive budget-recursion REFUTED for this shape,
  machine-checked. The missing piece is exactly `Provable k φ` at the fixpoint (= what Critch
  builds via diagonal lemma).
- **S3′ DONE — SETTLES route (B) NEGATIVELY (machine-checked, rfl, no sorry):** `k'=k` is
  FORCED by `eval`'s `.search` rule (Dynamics.lean:34-37): `CupodBot k = .search k …`, eval
  consults `proofSearch k` at the bot's OWN budget k, guard fires iff `Provable k (guard)`,
  so the sound box premise is `□_k` with k = bot's k. The `c_guard k` cost is internal
  proof-length bookkeeping paid ON TOP of the atom, NEVER subtracted from the antecedent box.
  No strictly-smaller premise → budget-recursion has no foothold → **route (B) CLOSED.** Not
  a Gödel wall; faithful to Critch (at the fixpoint the only proof is the diagonal/Löb
  fixpoint, unbuildable by budget-recursion).
- **CONCLUSION: constructive bounded Löb to make eval computable on the fixpoints is
  IMPOSSIBLE as designed.** Honest ceiling = route (A): keep PBLT axiom OR mechanize Critch's
  classical chain over abstract BoundedProvabilitySystem interface (§4b). eval stays
  noncomputable on genuine fixpoints — exactly what shipped evalC (option D) reflects (none
  there). The boundary is now PROVEN, not asserted — paper-grade: "the Löb fixpoints are
  exactly where bounded provability can't be made computable, because search budget = box
  budget coincide."
- **Still bankable & independent:** S2 `DecidablePred (Provable_finite k)` (decidable
  finite-proof fragment — real positive result, does NOT extend to fixpoints); eliminating
  `atom_complete_false_guard`.
- **S2 bankable & independent:** `DecidablePred (Provable_finite k)` by enumeration — do next
  regardless. Same for eliminating `atom_complete_false_guard`.

Full design + S1/S3 logs + revised §7:
`engine/PrisonersDilemma/Research/Notes/CONSTRUCTIVE_BOUNDED_LOB.md`. Quantifier decision:
stay meta-∀ (Formula has no ∀ constructor). See [[project_computable_eval_routeii]].

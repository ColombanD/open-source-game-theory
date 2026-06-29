# Walls and Extensions — the axiom/computability boundaries

A brief map of *where* the engine hits a wall, *why*, and *what would (or provably would not)*
remove it. Deeper write-ups: `COMPUTABLE_EVAL_NOTES.md`, `CONSTRUCTIVE_BOUNDED_LOB.md`.

The unifying theme is a **proof-vs-witness gap**: a fact can be *true in the `interp` model* yet
have *no finite proof TERM*. Every wall below is one facet of that gap.

---

## The 3 axioms (was 4 — `box_provable` ELIMINATED 2026-06-29)

All three are interp-**sound**; they are axioms only because `Derivation` has no *fixpoint*
box-introduction constructor, so a fixpoint witness can't be built structurally. (Plain
box-introduction DOES exist as constructors — `atomBoxImpl` for the witnessed atom, and now
`boxIntro` for bare necessitation; see the box-introduction section.)

| Axiom | Role | Removable? |
|---|---|---|
| `PBLT` | Parametric Bounded Löb (Critch 3.6); closes the `∀k` cooperation families | Mechanizable **faithfully (route A)** — but stays classical/existential. NOT the constructive lever. |
| `boxInternalize` | Box-internalization at fixed budget `k`; closes the 3 cross-bot fixpoints via `mutual_loeb` | **Conditionally** — needs the K-DISTRIBUTION (`□φ→□α`) form + a size-matching obligation per `mutual_loeb` leg (next target). Sound today tautologically (`interp := hfitD`). |
| `atom_complete_false_guard` | Π₁ residue: a play branching on a *failed* guard has a cert | **NO — proven irreducible** (Wall 2 below). Load-bearing (~5 false-guard else-plays). |

**`box_provable` (bounded GL-4 / necessitation) — REMOVED, now the THEOREM `BaseTheorems.box_provable`
(`#print axioms`: depends on NONE).** Discharged by a LOCAL box-introduction constructor
`Provable.boxIntro` (Derivation.lean), built directly from the premise `Provable k φ` with output
budget bounded by `(.box k φ).size`. **This did NOT need the size-indexed `Derivation` refactor** —
the engine's cost model is conclusion-`Formula.size` (not proof-tree size), so no structural index
was required (see the box-introduction section for the re-scoping that found this). Safe (premise is
genuine `Provable`, so nothing false is boxed — unlike the removed-unsound `atom_box_provable_impl`).

(`atom_box_provable_impl` was **removed** as unsound; its sound content survives as a theorem +
the `atomBoxImpl` rule. `c_guard_mono` was demoted axiom→theorem.)

---

## Wall 1 — Computable `eval`: blocked ONLY at the genuine Löb fixpoints

`eval` is `noncomputable` because its `.search` guard consults
`proofSearch k φ := decide (Provable k φ)`, and `Provable` is a `Prop` with axiom-injected
(term-free) members ⇒ `decide` needs `Classical`.

- **Off the fixpoints:** effectively computable. A finite proof term exists; the
  finite-proof fragment `Provable_finite k` is **decidable by enumeration** (S2). Shipped:
  `evalC` (option D) commits a real action with a finite witness here.
- **AT the genuine fixpoints** (FairBot↔FairBot, CUPOD↔CUPOD): **proven impossible**
  (`BoundedLobSpike` S3′, machine-checked). The constructive bounded-Löb lever (route B) is dead
  because **search budget = box budget coincide**: `eval` consults `proofSearch k` at the bot's
  OWN `k`, the sound premise is `□_k φ → φ` at the *same* `k`, and the `c_guard k` cost is
  internal proof-length bookkeeping paid *on top of* the atom, never subtracted from the
  antecedent box. No strictly-smaller budget ⇒ budget-recursion has no foothold ⇒ the fixpoint
  certificate would need *itself* as a `search_t` premise (forbidden: `PlaysProof` is a *least*
  fixed point).

**Net:** `eval` is computable everywhere a finite witness exists and **provably non-computable
exactly at the Löb fixpoints** — which is precisely where `evalC` returns `none`. The boundary is
located, not a failure.

### Route A vs Route B (do not conflate)
- **(A) Faithful PBLT** = explicit/honest axiom surface. Classical, existential, **does NOT make
  `eval` computable** — it only moves the IOU into the abstract derivability-condition interface.
- **(B) Constructive bounded Löb** = the lever that *would* make eval computable (builds a
  size-≤-k term). A theorem Critch never proved. **Ruled out (S3′)** for the reason above.

---

## Wall 2 — `atom_complete_false_guard`: irreducible (a DIFFERENT wall)

Same proof-vs-witness flavor, different cause. This is about a *negative* / *empty-certificate*
fact, not a positive fixpoint.

- **The fact is DECIDABLE** — `ppSize` / `Provable_fin` (`ComputableEval/PlaysCheck.lean`) compute
  "no size-≤-k `PlaysProof` of the guard exists" by a terminating procedure.
- **Wall 1 (positivity) — LIFTED.** With `Provable_fin` defined before the mutual block
  (cycle-break), a `search_f` constructor carrying `decide (Provable_fin k guard) = false`
  typechecks.
- **Wall 2 (soundness) — NOT lifted.** `Provable_fin = false ⇏ proofSearch = false` *at a
  fixpoint* (`Provable_fin` false while `Provable`/`proofSearch` is PBLT-axiom-true), and `eval`
  can't be rewired to `Provable_fin` because the PBLT cooperations need `proofSearch = true`
  there.
- **Exclusion Lemma (machine-checked, `[propext]`, root-imported in
  `ComputableEval/Exclusion.lean`)**: `no_deriv_else` / `provable_else_isAtom` — no `PlaysProof`
  concludes a search-bot's ELSE-action ⇒ the else-play's **certificate type is provably empty**. The
  axiom inhabits a true `interp` consequence that has *no term at all*. The honest premise
  `¬ Provable k guard` is a Π₁ negation, kernel-non-positive in the mutual block.

**Net:** removing the axiom needs a `PlaysProof` rule producing the else-action soundly — blocked
by Walls 1+2. The *fact* is decidable and the witness is shipped, but it cannot be *carried* as an
in-`PlaysProof` term at this architecture.

### Concrete win banked
The `.impl`-guard false fragment IS dischargeable without the axiom when the consequent is a false
*atom* (refuted by `Provable_sound`): `CIMCIC vs DefectBot`, `DIMCID vs CooperateBot` are real
outcome theorems with NO reflection axiom. *Play*-atom false guards (DupocBot/JustBot/CupodTrollBot)
still route through the axiom — no false-consequent handle.

---

## How the two walls relate

| | What's blocked | Why | Scope |
|---|---|---|---|
| **Wall 1 — computable eval** | the *positive* fixpoint cooperation cert | budget coincidence (search k = box k); least-fixpoint forbids self-premise | only at genuine Löb fixpoints |
| **Wall 2 — false-guard axiom** | the *negative* else-play cert | certificate type provably empty; Π₁ negation non-positive | the ~5 false-guard else-plays |

Both are the proof-vs-witness gap; one positive, one negative. Both **proven**, not unattempted.

---

## Box-introduction in `Derivation`/`Provable` — what was tried

"Box-intro" is not one thing. It comes in four flavors. This is the representational gap the
`box_provable` (now removed) / `boxInternalize` axioms cite.

**KEY RE-SCOPING (2026-06-29, `FormulaSizeBoxIntroSpike.lean`).** The engine's cost model is
conclusion-`Formula.size` (`Derivation.size := conclusion.size`), NOT proof-tree size. `box_provable`
and `mutual_loeb` discharge their budget obligations entirely through `Formula.size` side-conditions,
which need NO structural index on `Derivation`. The real blocker for box-intro was never a missing
size index — it was a **missing box-introduction constructor** (`no_box_headed_deriv`: no `Derivation`
concludes a `.box`-headed formula, even via `modusPonens`). So the ~500-ref size-index refactor was
testing the WRONG lever; the fix is a LOCAL constructor on `Provable`.

| Flavor | What it is | Status |
|---|---|---|
| **Bare unwitnessed atom** | `φ → □_k φ` for an arbitrary atom | **TRIED → REMOVED, unsound.** Was `atom_box_provable_impl`: its interp forces a size-≤-k cert whenever the play happens at *some* fuel — false. |
| **Witnessed atom** | box the atom only when an `AtomProvable` witness is already held | **SHIPPED, no axiom.** The `atomBoxImpl` constructor (`Derivation.lean`). |
| **Bare necessitation** | `Provable k φ → □_k φ` (premise is genuine provability) | **SHIPPED 2026-06-29, no axiom — this is what KILLED `box_provable`.** The `boxIntro` constructor (`Derivation.lean`): output budget bounded by `(.box k φ).size`, `Provable_sound` arm is the identity (`interp (.box k φ) := Provable k φ`). SAFE — premise is genuine `Provable`, inert on false atoms. |
| **Fixpoint (unwitnessed cooperation)** | box the cooperative atom at a Löb fixpoint | **TRIED two ways (spiked), settled with `boxInternalize`** — see below. Still axiom. |

**The fixpoint case (`MutualLobSpike.lean`, machine-checked):**
- **Route 1** (chain bare outputs): FAILS — only *relocates* the bare-atom box-intro (φP→φD);
  `box_provable` can't supply `Provable k (φD → □_k φD)` on the bare unwitnessed atom.
- **Route 2** (Critch's move: necessitate the *proved* leg via `box_provable`, then distribute
  with object axiom-4 + axiom-K): **COMPILES with no `sorry`** — but the honest cost is **TWO new
  sound axioms** (a budget-inflating object axiom-4 + an **atom-restricted axiom-K**; full object-K
  is the incomplete direction, sound only for play-atoms).
- **Not adopted as written.** What shipped instead is `boxInternalize` — a fixed-budget,
  meta-level *internalization transformer* (not a constructor), tautologically sound
  (`interp := hfitD`), which closes the three cross-bot fixpoints via `mutual_loeb`.
- The faithful **object-antecedent GL-K** (a "real" constructor-level box-intro-with-K) is a
  **machine-confirmed dead end** (`HonestKSpike.lean`): sound only with an existential output box
  budget = cert cost, which can't be reconciled to the `k` that PBLT + the opponent leg demand;
  bridging `□_{cert} α → □_k α` needs unsound box-index weakening.

**Net:** constructor-level box-intro now exists for the *witnessed* atom (`atomBoxImpl`) AND for
*bare necessitation* (`boxIntro`, which discharged `box_provable`). For the *fixpoint*, the missing
piece is the K-DISTRIBUTION `□φ → □α` (not bare necessitation): `boxIntro` gives `□(φ→α)` but not the
distributed `□φ → □α` that `mutual_loeb` consumes. A same-`k` GL axiom-K constructor for this is sound
(gate spike `SizeIndexBoxIntroSpike.lean`: false atom stays underivable) but carries a per-leg
size-matching obligation (the `HonestKSpike` budget wall, relocated to a `Formula.size` equality, not
unsoundness). That is the next box-intro target — and, like `box_provable`, it does NOT need the
size-index refactor (the obligation is in `Formula.size`, the engine's existing currency).

---

## Possible extensions (and dead ends)

**Bankable, independent of the walls:**
- `DecidablePred (Provable_finite k)` by enumeration (S2) — real positive result; does NOT extend
  to fixpoints.
- Faithful PBLT mechanization (route A) — cleans the axiom surface (4→honest interface); `eval`
  stays noncomputable at fixpoints. Mathlib gives only ~15–20% scaffolding (`ModelTheory`); no
  `Bew`, no bounded GL — the hard core is built from zero.

**Dead ends (machine-refuted — do not retry):**
- Constructive bounded Löb to make eval computable on fixpoints (route B) — S3′.
- `search_f` as a sound constructor — Wall 2 (soundness) + the Exclusion Lemma.
- Deciding `Provable k φ` by structural recursion on the program — `subst` of a `.search`-bot into
  its own guard raises search-depth (`DecMeasure.lean`).
- The `derivable`/`playsCheck` separate-search-gas checker — non-monotone.
- Faithful object-antecedent GL-K for the cross-bot fixpoints (existential output budget) — needs
  unsound box-index weakening (`HonestKSpike.lean`). The *same-`k`* GL-K is sound (gate spike) but
  carries a size-matching obligation — that's the live `boxInternalize` target, not a dead end.
- Bare-atom box-intro `φ → □_k φ` (the old `atom_box_provable_impl`) — unsound, removed.
- **The ~500-ref size-indexed `Derivation` refactor — SHELVED as unnecessary.** Re-scoping
  (`FormulaSizeBoxIntroSpike.lean`) found the engine uses conclusion-`Formula.size`, not proof-tree
  size, so box-intro is a LOCAL constructor (`boxIntro`, which discharged `box_provable`) — no
  re-index needed. Do not start the refactor.

**Shipped artifacts that sit exactly at each boundary (all root-imported, `[propext]`-clean):**
- `evalC` (`ComputableEval/Computable.lean`) — sound, total, computable *partial* evaluator; `none`
  exactly at the fixpoints.
- `ppSize` / `Provable_fin` / `instDecProvableFin` (`ComputableEval/PlaysCheck.lean`) — computable,
  sound decider for the bounded play-certificate.
- `no_deriv_else` / `provable_else_isAtom` / `decidablePred_provableFin`
  (`ComputableEval/Exclusion.lean`) — the **irreducibility proof** for `atom_complete_false_guard`
  (else-play certificate type provably empty) + the `DecidablePred (Provable_fin k)` named lemma.
  Promoted from scratch into the engine (Step 1, done).
- `Provable.boxIntro` (`Derivation.lean`) + `BaseTheorems.box_provable` (theorem, no axioms) — the
  **local box-introduction constructor that eliminated the `box_provable` axiom** (4 → 3),
  2026-06-29.

---

## Next steps

Progress: 4 axioms → **3** (`box_provable` eliminated 2026-06-29). The remaining three split into
`boxInternalize` (next, local — the K-distribution), `PBLT` (the deep Löb core, route A only), and
`atom_complete_false_guard` (proven irreducible). The order below reflects payoff-per-risk.

1. **Cheap, independent wins — DONE ✅ (`ComputableEval/Exclusion.lean`, root-imported,
   `[propext]`-clean).**
   - `decidablePred_provableFin` — `DecidablePred (Provable_fin k)`, the finite proof-TERM fragment,
     computing via `instDecProvableFin`.
   - `no_deriv_else` / `provable_else_isAtom` — the citable *proof* that
     `atom_complete_false_guard` is irreducible (else-play certificate type provably empty). Promoted
     from the (now-deleted) `ExclusionSpike`.

2. **`box_provable` eliminated — DONE ✅ (2026-06-29, 4 axioms → 3).** A LOCAL box-introduction
   constructor `Provable.boxIntro` (Derivation.lean) discharges it: `Provable k φ → □_k φ` with output
   budget bounded by `(.box k φ).size`, `Provable_sound` arm = identity, SAFE (premise is genuine
   `Provable`, inert on false atoms). `BaseTheorems.box_provable` depends on NO axioms; no headline
   theorem regressed (verified `#print axioms`). The size-index refactor was NOT needed — re-scoping
   found the engine uses conclusion-`Formula.size`. Build green, 3 axioms.

3. **`boxInternalize` — next axiom target (the K-distribution).** `boxIntro` gives `□(φ→α)` but not
   the distributed `□φ → □α` that `mutual_loeb` consumes. A same-`k` GL-K constructor for it is sound
   (gate spike `SizeIndexBoxIntroSpike.lean`) but carries a per-leg `Formula.size`-matching obligation
   (the `HonestKSpike` budget wall, relocated — NOT unsoundness). Local, like `boxIntro`; no refactor.
   Whether the per-leg size-matching discharges for the real `mutual_loeb` legs is the open question.

4. **`PBLT` — route A only.** The remaining (and deepest) axiom is the Löb core. Faithful mechanization
   (classical, existential) cleans the surface but leaves `eval` noncomputable at the fixpoints.
   The constructive route (B) stays closed (S3′). Separate, larger effort.

5. **Do NOT pursue** (settled): constructive bounded Löb for computable eval (S3′), `search_f` as a
   constructor (Walls 1+2 + Exclusion), program-recursion deciders, existential-budget object-GL-K,
   and the ~500-ref size-index refactor (shelved — unnecessary). Machine-refuted or superseded.

**What no next step changes:** `atom_complete_false_guard` stays irreducible, and `eval` stays
noncomputable at the genuine Löb fixpoints — both orthogonal to the box-intro work (`boxIntro` is
positive necessitation; the false-guard wall is the negative Π₁ cert, and the eval wall is budget
coincidence — neither touched).

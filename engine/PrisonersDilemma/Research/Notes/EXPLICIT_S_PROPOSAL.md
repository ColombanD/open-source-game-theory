# Proposal — making S explicit (concrete proof-terms)

**One-line goal.** Replace abstract-`Prop` provability with a **concrete, sized, enumerable
proof-term** representation, so the two remaining *reducible* reflection axioms (`boxInternalize`,
`PBLT`) become theorems. This is the single foundational lever the walls analysis identifies; see
`WALLS_AND_EXTENSIONS.md`.

Status going in: **3 axioms** (`atom_complete_false_guard`, `boxInternalize`, `PBLT`) after
`box_provable` was eliminated locally. This proposal targets `boxInternalize` and `PBLT`; the floor
it reaches is **1 axiom** (`atom_complete_false_guard` is irreducible even under explicit S — Wall 2).

---

## Why this, why now

Each remaining axiom is an axiom for a representational reason already machine-located:

- **`boxInternalize`** — its premise is a proof-*transformer* `Provable k φ → Provable k α`, a
  **non-positive occurrence** the kernel rejects as a constructor (Wall 3, proven). It is *not*
  removable locally. But with proofs as concrete data the transformer becomes a positive proof-TERM
  ingredient, and box-internalization is a theorem — **machine-checked sound, no axioms** in the toy
  `ExplicitSBoxInternalizeSpike.lean`.
- **`PBLT`** — Critch's parametric bounded Löb. The faithful (route A) mechanization is a classical
  diagonal argument that needs a concrete encoding of provability to even state. Same lever.

So both collapse under one change: **proofs become data.** This is de-risked now in a way it was not
before — Phase 1's payoff is already toy-proven.

**What it does NOT buy** (state up front): `eval` stays noncomputable *at* the Löb fixpoints (route B
closed, S3′), and `atom_complete_false_guard` stays irreducible (empty else-cert, not abstractness).
Floor = **1 axiom**, not 0. The win is axioms 3 → 1 and a cleaner, enumerable proof system.

---

## The minimal shape

1. **A sized proof-term type.** Keep `Derivation`/`PlaysProof`/`Provable` as the proof objects, but
   give `Derivation` a **structural** size index (or a real `Deriv.size` recursion) instead of the
   current shortcut `Derivation.size φ := φ.size` (conclusion-character count). The structural size is
   what makes "proofs of size ≤ k" a *finite* set.

2. **Bounded provability as decidable enumeration.** `Provable_k φ := ∃ d : Deriv φ, d.size ≤ k`,
   with a `Decidable` instance by enumerating size-≤-k terms. Seed already exists: `Provable_fin` /
   `ppSize` (`PlaysCheck.lean`) decide the play-atom fragment — generalize to all of `Deriv`.

3. **Keep the abstract API as a bridge.** Prove `Provable_k ↔ Provable` so downstream theorems don't
   all rewrite at once. This is what turns a big-bang refactor into an incremental one.

---

## Phased plan (de-risk before the valley)

### Phase 0 — size-index `Deriv` + decidable `Provable_k`, behind the existing API
The mechanical, ~500-ref part. Concentrated, not uniform — blast radius (root lib, measured):

| File | refs | role |
|---|---|---|
| `Derivation.lean` | 111 | the type + size + (3) `.rec` consumers |
| `BaseTheorems.lean` | 94 | `Provable_sound`, `proofSearch_*`, `mutual_loeb`; `.rec` + `.struct` + `.size` |
| `Theorems/LlmGenerations/PrudentBot.lean` | 71 | `.struct` proof-building |
| `Axioms.lean` | 44 | axiom statements (shrinks) |
| `JustBot.lean` / `PlaysCheck.lean` / `DupocBot.lean` / `CupodBot.lean` / `CIMCIC` / `Exclusion` / `DIMCID` | 14–38 each | `.struct` / `.rec` / size bounds |

- **`.rec` sites needing new arms: only 3** (`BaseTheorems.lean`, `CIMCIC.lean`, `DIMCID.lean`) —
  same sites that already took the `boxIntro` arm, so the pattern is known.
- **The one real decision:** `Derivation.size` is currently `:= conclusion.size`. Phase 0 either
  (a) adds a *separate* structural size used only by `Provable_k`, leaving the conclusion-size
  machinery intact (smaller diff, two sizes coexist), or (b) replaces it wholesale (cleaner, larger
  diff, must re-prove every `d.size ≤ k` bound — `CupodBot`'s `5·log2 k + 33 ≤ k`, etc.).
  **Recommend (a)** — minimize the valley; the structural size is additive, not a replacement.
- **Exit criterion:** `Provable_k ↔ Provable` proven, `instDecidable (Provable_k k φ)` computes, full
  build green, **axioms unchanged (still 3).** No payoff yet — this phase only builds the substrate.
- **Risk:** mechanical but long red-build. Mitigate by doing it on a branch, file-by-file in
  dependency order (`Derivation` → `BaseTheorems` → bots/theorems), keeping the abstract API as the
  bridge so leaf theorems compile untouched until the end.

### Phase 1 — `boxInternalize` → theorem (the cheap, high-confidence win)
Already toy-proven (`ExplicitSBoxInternalizeSpike.lean`: `axK ∘ boxIntro`, no axioms, sound).
- Add a GL axiom-`K` rule whose premise is the positive proof-TERM `Deriv (□(φ→α))` (legal once
  Phase 0 exists), derive `boxInternalize` as a theorem, delete the axiom, repoint `mutual_loeb`.
- **Per-leg obligation:** the boxed sub-proofs must reconcile to the same budget `k` — a
  `Formula.size`-matching proof per `mutual_loeb` leg (trivial in the toy because `axK` keeps boxes
  at `k`; real but sound at scale). 3 legs (PrudentBot↔DupocBot guises).
- **Exit:** axioms **3 → 2**, build green, `mutual_loeb` consumers unchanged.

### Phase 2 — `PBLT` route A (the genuine research piece)
Faithful classical mechanization of Critch Lemma 3.6 over the explicit encoding.
- Mathlib gives ~15–20% scaffolding (`ModelTheory`); **no** bounded GL, no arithmetized provability,
  no derivability conditions — the hard core is built from zero.
- Stays **classical/existential** (does NOT make eval computable; route B is closed).
- **Exit:** axioms **2 → 1**. This is a separate, larger effort; not gated on Phase 1.

---

## De-risk status (what's proven vs. open)

| Piece | Status |
|---|---|
| `boxInternalize` removable under explicit S | **toy-proven, sound, no axioms** (`ExplicitSBoxInternalizeSpike`) |
| `Provable_finite` decidable by enumeration | **proven on the play-atom fragment** (`ppSize`/`Provable_fin`, shipped); generalization is engineering |
| Phase 0 mechanical viability | seed exists (`Provable_fin`); the `.rec`/`.struct`/size pattern is known (3 `.rec` sites) |
| Per-leg budget-reconciliation at scale | **open** — trivial in toy, unproven for the 3 real `mutual_loeb` legs |
| `PBLT` route A | **open** — standard but from-zero; classical only |
| Floor reachable | **1 axiom** (`atom_complete_false_guard` irreducible, Wall 2) |

---

## Recommendation

The order is **Phase 0 → Phase 1 → Phase 2**, but the decision gate is Phase 0: it's the only
expensive-and-mechanical part, and its payoff (Phase 1) is already de-risked. If the budget for a
long red-build valley exists, Phase 0+1 is a concrete, bounded path to **2 axioms** with a
machine-checked payoff. Phase 2 (`PBLT`) is a separate research commitment.

If the valley is not worth it now: the current **3-axiom** state is already a clean, defensible
result — `box_provable` removed locally, `boxInternalize`/`PBLT` proven removable-only-by-explicit-S,
`atom_complete_false_guard` proven irreducible. Explicit S is the stated next lever, fully scoped
here, ready when the time is right.

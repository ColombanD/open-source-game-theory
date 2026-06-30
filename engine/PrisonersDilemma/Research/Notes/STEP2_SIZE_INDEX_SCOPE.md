# Step 2 scope — the size-indexed `Derivation` gate spike

**Purpose.** A go/no-go decision spike, NOT a shippable artifact. It must answer one question before
the ~500-ref full refactor is committed:

> If the box budget is a *tracked index* on the proof object (rather than a free `Nat` argument to
> `Formula.box`), can `box_provable` and `boxInternalize` be re-derived as **constructive theorems**
> (with exhibited proof terms), discharging two of the four axioms?

If the toy says **no**, abort — the refactor's entire value is contingent on this. If **yes**, the
full refactor is justified and we know the shape that works.

This note is grounded in the real engine (read 2026-06-29), not memory.

---

## What the two target axioms actually do (the thing the spike must reproduce)

Both live in `Axioms.lean`; their consumers are in `BaseTheorems.lean` + `Theorems/.../PrudentBot.lean`.

- **`box_provable`** : `Provable k φ → ∃ K, K ≤ (□_k φ).size ∧ Provable K (□_k φ)`.
  Bounded GL-4 / necessitation. Consumed by `atom_box_provable_impl_sound` (BaseTheorems.lean:444):
  `box_provable k (.plays p q a) hatom` to box a *witnessed* play-atom. NO fixpoint here — this is
  the Σ₁-completeness step. **This is the easier target.**

- **`boxInternalize`** : `(Provable k φ → Provable k α) → size → Provable k (□_k φ → □_k α)`
  for a play-atom `α`. Internalizes a budget-`k` proof *transformer* into an object box implication.
  Consumed by `mutual_loeb` (BaseTheorems.lean:493→502) which feeds it the cross-bot transformer
  `hfitD : Provable k φP → Provable k φD` to close the fixpoints. **This is the fixpoint target.**

Why they're axioms TODAY (real reason, from `Derivation.lean` + Axioms.lean docs): the `Provable`
inductive has **no box-introduction constructor**, and `Formula.box : Nat → Formula → Formula`
carries the budget as a *plain `Nat` payload* on the formula — the proof object `Provable k (□_m φ)`
does not relate `k`, `m`, and the *cost* of the boxed sub-proof. So a constructor `Provable k φ →
Provable K (□_k φ)` cannot compute `K` from the structure of the input proof — there is nothing to
recurse on that tracks proof size as an index.

---

## The architecture under test

Current block (`Derivation.lean`):
- `Derivation : Formula → Type` (8 ctors; `.size` is a *function* on the term).
- `PlaysProof : Prog³ → Action → Nat → Prop` — **already cost-indexed** (the trailing `Nat n`).
- `AtomProvable : Nat → Formula → Prop` — `mk : PlaysProof … n → n ≤ k → AtomProvable k (.plays …)`.
- `Provable : Nat → Formula → Prop` — 6 ctors (`struct/atom/weakenImpl/searchThenSearch_t/
  implTrans/atomBoxImpl`).

**Key observation (de-risks the spike):** `PlaysProof` is *already* size-indexed. The missing index
is on `Derivation`/`Provable` — specifically a relation between the **boxed budget** and the
**cost of the sub-proof being boxed**. So the spike does NOT need to re-architect `PlaysProof`; it
needs a `Derivation`/`Provable` whose box-conclusions carry a verifiable size relation.

**Proposed toy shape** (smallest fragment that exercises the question):
- A toy `Formula` with just `.plays` (an opaque atom), `.impl`, `.box (k : Nat)`.
- A toy `TProvable : Nat → TFormula → Prop` with **`.size`-indexed `Derivation` analogue** — i.e.
  the structural proofs carry a size the box-intro ctor can read.
- A candidate **box-intro constructor** `boxI : TProvable k φ → (cost relation) → TProvable K (□_k φ)`
  where `K` is *computed from* the input proof's tracked size — the thing impossible today.

---

## Success / abort criteria (the gate)

**PASS (justifies the full refactor)** requires BOTH:
1. **`box_provable` analogue is a constructive theorem on the toy** — `boxI` typechecks as a real
   constructor (kernel-positive), and the necessitation lemma `TProvable k φ → ∃K, TProvable K (□_k φ)`
   is proven by recursion on the size-indexed proof, NO axiom, `#print axioms` ⊆ {propext, Quot.sound}.
2. **`boxInternalize` analogue is reachable for the fixpoint transformer** — given a toy transformer
   `TProvable k φ → TProvable k α`, the object `TProvable k (□_k φ → □_k α)` is derivable WITHOUT a
   tautological-`:= hfitD` axiom, i.e. genuinely built from the size-indexed box-intro. Crucially:
   it must stay **sound** (no false atom becomes provable — test: the toy DefectBot-cooperates atom
   must remain underivable).

**ABORT** if EITHER:
- the box-intro ctor is non-positive / can't compute `K` even with the index (the index doesn't
  actually break the representational block); OR
- the fixpoint internalization still requires a witness-free assertion (the budget-coincidence wall,
  Wall 1 of the eval crux, re-appears at the *proof-system* level — i.e. the boxed transformer needs
  a budget that can't be reconciled to `k`, exactly the `HonestKSpike` failure). If this reappears,
  the refactor moves `boxInternalize` but does NOT eliminate it — NOT worth ~500 refs.

**Explicitly OUT of scope for the gate** (do not let these block a PASS):
- `PBLT` itself (Step 3, separate; the constructive Löb route B is already closed by S3′).
- `atom_complete_false_guard` (proven irreducible, Step 1; size-index lifts its Wall 1 not Wall 2).
- Re-proving any real outcome theorem. The toy only needs the two box rules + a soundness probe.

---

## Risks & known traps (from prior spikes — do not re-walk)

- **The `:= hfitD` tautology trap.** `boxInternalize` is sound today *because* its interp is
  definitionally its own hypothesis. A constructive box-intro must NOT smuggle this back — if the
  toy "constructive" rule is secretly `:= hfitD`, it proves nothing. The soundness probe (DefectBot
  atom stays underivable) is what catches this.
- **Budget non-composition** (`MutualLobSpike.lean`, `HonestKSpike.lean`): separate object K + 4 +
  necessitation have existential budgets that don't align to the fixed `k` PBLT + the opponent leg
  demand. The size-index must make `K` *computable and ≤-bounded*, not merely existential, or the
  same wall returns.
- **`PlaysProof` is already indexed** — don't duplicate its cost machinery; reuse the pattern.

---

## Estimated effort

- Toy spike (this gate): ~half a day to a day. Non-root scratch
  (`Research/Spikes/bounded_lob/SizeIndexBoxIntroSpike.lean`), `lake env lean`, not imported.
- IF PASS → full refactor: ~500 refs across the 17 files touching `Derivation`/`PlaysProof`/
  `Provable`, long red-build valley. Separate decision after the gate.

## Deliverable of the gate

A one-paragraph PASS/ABORT verdict appended here + to `WALLS_AND_EXTENSIONS.md` Step 2, with the
`#print axioms` evidence. No engine changes land from the gate itself.

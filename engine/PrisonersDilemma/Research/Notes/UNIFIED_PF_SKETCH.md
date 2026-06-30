# Sketch — what unifying `Derivation`/`Provable` into one `Pf` would do

A paper exercise (NO engine change). Shows the merged proof-term type, what it removes, and what two
of the real bots' proofs would look like before/after. Companion: `EXPLICIT_S_PROPOSAL.md`.

## The current shape (what bugs you)

Reasoning is split across **two** types by the `Type`/`Prop` boundary, with `Provable` gluing them:

```
Derivation : Formula → Type            Provable : Nat → Formula → Prop
  modusPonens   ─┐                       struct  (wraps a Derivation)   ← glue
  hypSyll        │  reasoning,            atom    (wraps an AtomProvable)← glue
  searchBranch   │  but split             weakenImpl
  simStep        │  by Type/Prop          searchThenSearch_t            ┐
  botSimStep     │                        implTrans                     │ same ideas
  botSearchStep  │                        atomBoxImpl                   │ as the
  iteBranchSearch_t                       boxIntro / app / axK / box4   ┘ left column
  eqRefl        ─┘
```

The **duplication** is the eyesore — each is the same idea, twice, because a `Type`-valued
`Derivation` cannot carry a `Prop`-valued `Provable` premise:

| `Derivation` (Type) | `Provable` (Prop) twin | the idea |
|---|---|---|
| `modusPonens`        | `app`                  | modus ponens |
| `hypSyll`            | `implTrans`            | implication transitivity |
| `searchBranch`       | `searchThenSearch_t`   | read a `.search` guard |
| (none — would be a `Derivation` GL rule) | `boxIntro`/`axK`/`box4` | the box / HBL rules |
| `struct` / `atom`    | —                      | **pure glue**: exist only to embed one type in the other |

So: 8 `Derivation` constructors + 13 `Provable` members, of which `struct`/`atom` are glue and ~4
pairs are duplicates. ~21 constructors, ~5 of them redundant.

## The unified type `Pf`

Make provability ONE concrete proof-term datatype carrying its own budget. (`PlaysProof` stays — see
below; it is execution, not reasoning.)

```lean
inductive Pf : Nat → Formula → Type where         -- "Pf k φ" = a size-≤-k proof TERM of φ
  -- entry from execution (the ONLY surviving bridge; `struct`/`atom` glue is GONE):
  | atom  : PlaysProof me opp me a n → n ≤ k → Pf k (.plays me opp a)
  -- ── logical core (ONE modus ponens, ONE transitivity — no Type/Prop twins) ──
  | mp    : Pf k (.impl φ ψ) → Pf k φ → Pf k ψ
  | hypSyll : Pf k (.impl φ ψ) → Pf k (.impl ψ χ) → Pf k (.impl φ χ)
  | weaken  : Pf k ψ → Pf k (.impl φ ψ)             -- true-consequent (was `weakenImpl`)
  -- ── source transparency (UNCHANGED in spirit — S reads `Prog`) ──
  | searchBranch …  | simStep …  | botSimStep …  | botSearchStep …  | iteBranchSearch …  | eqRefl …
  -- ── box / HBL rules (now siblings of the structural rules, not a separate tier) ──
  | boxIntro : Pf kIn φ → Pf k (.box kIn φ)
  | axK      : Pf k (.box k (.impl φ α)) → Pf k (.impl (.box k φ) (.box k α))
  | box4     : Pf k (.impl (.box k φ) (.box k (.box k φ)))
  | atomBoxImpl …
```

**What vanished:**
- `Derivation` as a separate type — merged in.
- `Provable.struct` / `Provable.atom` — the glue is gone (no second type to embed). `atom` above is
  the *one* remaining execution bridge, not glue between two reasoning types.
- the `modusPonens`/`app` and `hypSyll`/`implTrans` and `searchBranch`/`searchThenSearch_t` **pairs**
  collapse to ONE each. (`searchThenSearch_t` becomes a derived lemma — `searchBranch` then `mp` on
  the prudence atom — rather than a primitive.)

~21 constructors → ~13, the ~5 redundant ones gone. One proof type, one MP, one transitivity.

**What GAINS a constructor (the honest cost):** to actually prove PBLT you'd ALSO add the deduction
theorem (`impI : (Pf k φ → Pf k ψ) → Pf k (.impl φ ψ)`) and Gödel machinery — that's the heavier
logic, separate from the tidying. The tidying above is free of those; they ride along only if you go
all the way to PBLT-removal.

## What it does to the BOTS (the part you asked for)

The bot *statements* (`outcome_X_vs_Y = some (a,b)`) are UNCHANGED — they mention `play`/`outcome`,
not `Provable`. Only the *proof internals* that touch `Provable`/`Derivation` change. Two real cases:

### CIMCIC vs DefectBot (the `Forbidden`-motive / `.struct` exclusion proof)

CURRENT (`CIMCIC.lean`): `cimcic_no_provable_forbidden` drives `Provable.rec` and must list an arm
for EVERY `Provable` member — including `struct` (which obtains a `Derivation` and recurses into a
SECOND induction `cimcic_no_deriv_forbidden`) plus `atom`, `weakenImpl`, `searchThenSearch_t`,
`implTrans`, `atomBoxImpl`, `boxIntro`, `app`, `axK`, `box4` — **two nested inductions** (over
`Provable` AND over `Derivation`), ~12 arms.

UNIFIED: ONE induction over `Pf`. The `struct`→`Derivation` hop disappears (no second type), so
`cimcic_no_deriv_forbidden` MERGES into the single `Pf` induction. ~12 arms over two types →
~10 arms over one type, no nesting. The `app`/`mp` and `hypSyll`/`implTrans` arms that were
duplicated become single arms. **Net: the proof gets shorter and loses the "why are there two
inductions?" confusion** — which is exactly the messiness you flagged.

### PrudentBot↔DupocBot (the cooperation, `mutual_loeb` + the leg construction)

CURRENT (`PrudentBot.lean`): a leg is built as
`Provable.struct ⟨Derivation.searchBranch …, size-proof⟩` — you reach *through* the `struct`/
`Derivation` glue to get at the real rule. Then `mutual_loeb` chains `boxIntro`/`axK`/`box4`/
`implTrans` (Provable-level) over those legs.

UNIFIED: the leg is just `Pf.searchBranch …` — no `struct ⟨…⟩` wrapper, no embedding ceremony.
`mutual_loeb`'s chain is identical in shape (boxIntro/axK/box4/implTrans are the same rules) but
they're now siblings of `searchBranch`, so there's no "Derivation rule vs Provable rule, which layer
am I on?" friction. **The cooperation proof reads as one flat chain instead of a layered one.**

### The size side-conditions — UNCHANGED

Every `… .size ≤ k` obligation stays exactly the same (the cost model is still conclusion-
`Formula.size`). So the `simp [Formula.size]; omega` lines in every bot proof are byte-identical.
The unification touches *structure*, not the budget arithmetic.

## Honest scorecard

| | unify-only (tidying) | unify as part of PBLT-removal |
|---|---|---|
| `Derivation`/`Provable` duplication | **gone** | gone |
| `struct`/`atom` glue | **gone** | gone |
| bot proofs | **shorter, flatter** (re-proved, but easier) | same + heavier logic |
| `PlaysProof` (execution bridge) | **stays** (intrinsic) | stays |
| deduction theorem + Gödel `Bew` | not added | **added** (the cost) |
| axiom count | still 2 | → 1 (PBLT removed) |
| effort | **re-prove the whole engine** in the merged type | that + the encoding |

## Verdict

Unifying genuinely fixes the thing that reads as "inconsistent": the Type/Prop reasoning split and
the `struct`/`atom` glue. The bot proofs would get **shorter and flatter** (one induction, one MP, no
embedding ceremony). BUT it requires re-proving the entire engine against `Pf`, and for *tidiness
alone* that cost is not worth it — the comment cleanup already bought ~80% of the legibility.

It IS worth it **bundled with PBLT-removal**: there you're rebuilding the proof layer anyway, the
unification comes for free, and you also gain the deduction theorem / encoding the merged type needs.
So the tidiness and the PBLT motivations point the same way — unify if and when you do explicit-S,
not before.

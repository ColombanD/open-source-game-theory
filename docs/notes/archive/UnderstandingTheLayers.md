# Understanding the Layers

A short conceptual map of the engine: the layers it is built from, the objects
related to "proof", and the meta-level / object-level distinction. Written as a
study aid after the reform that made the proof system `S` explicit; refreshed
2026-09-04 for the current engine (one proof-term type `Pf`, zero project axioms).

> **Notation.** `⊢_k φ` is `Pf k φ` — `S` derives `φ` at budget `k`; `⊨ φ` is
> `φ.interp` — `φ` is true of the evaluator; the meta level (Lean) has no symbol.
> Fixed in `PROVABILITY_NOTATION.md`, the companion to this note.

## The layers (bottom to top)

| Layer | What it is | Formal system | Notation | Key objects |
|---|---|---|---|---|
| **0. Programs** | the agents, as *source code* | none (it's syntax + an evaluator) | — | `Prog`; `eval`/`play`/`outcome` |
| **1. `S`** | the logic the *agents* reason in | the proof system `S` | `⊢_k φ` | `Formula`, `Pf` (with `PlaysProof`/`AtomProvable`), `proofSearch` |
| **2. Meta** | the logic *we* prove outcomes in | Lean / CIC | prose only; `⊨ φ` names a Lean `Prop` | `theorem …`, `Formula.interp`, `sound_upto` |

- **Layer 0 — `Prog`.** Pure source code (Critch's Python-pseudocode bots). No
  constructor yields an `Action` directly; actions appear only by running code
  via `eval` (Dynamics.lean). Bots: `CupodBot`, `CIMCIC`, ….
- **Layer 1 — `S`, where the proof system lives.** When a bot does
  `.search k φ …` it asks an oracle to *derive a `Formula`*. `S` is the system
  that answers. **`S = (Pf, proofSearch)`**, speaking the language `Formula`:
  `Pf k φ` (ProofSystem.lean) is the ONE proof-term type — 33 constructors, the
  play-atom half being the mutual `PlaysProof`/`AtomProvable` block — and
  `⊢_k φ` is its shorthand. This is the logic agents use to reason *about each
  other*.
- **Layer 2 — the meta-theory.** Lean itself. When we write
  `theorem outcome_CupodBot_vs_CupodBot …` we reason *about* layers 0 and 1. Its
  axioms are Lean's three (`propext`, `Classical.choice`, `Quot.sound`) — the
  engine adds NONE (zero project axioms since 2026-07-03).

**Where is `S`? Layer 1.** Not Lean (that's the meta-layer above it), not `Prog`
(those are the programs it reasons about). `S` sits *between*: agents (L0) call
`S` (L1) via `proofSearch`; we (L2) reason about `S` via `interp` + soundness.

## The objects linked to "proof" (one fact, four guises)

For a single fact "`S` derives φ within budget `k`" — `⊢_k φ`:

| Object | Type | Notation | Role |
|---|---|---|---|
| `Pf k φ` | `Prop` (mutual inductive with `PlaysProof`/`AtomProvable`) | `⊢_k φ` | the **`S`-derivation**: a term `h : Pf k φ` IS the proof tree, transcript ≤ `k` (costs are cumulative — a premise's transcript is a summand of the conclusion's) |
| `proofSearch k φ` | `Bool` | — | the oracle's **yes/no**, `:= decide (Pf k φ)` (classical, `noncomputable`; the computable `decFull`/`evalG` live in `Decidability/`) |
| `Formula.box k φ` | `Formula` | `□_k φ` | the **syntax** for provability inside `S`'s language — `S`'s own name for `⊢_k`, nestable |
| `φ.interp` | `Prop` | `⊨ φ` | **truth**: what `φ` says about the real evaluator; `⊨ □_k φ ≡ ⊢_k φ` by definition of `interp` on `.box` |

Chain: `Pf` (the derivation) → `proofSearch` (Bool reflection, what agents call);
`box` is the *syntactic name* whose meaning (`interp`) **is** `Pf`.

*History.* Until 2026-07-14 the derivation was split into `Derivation` (`Type`,
the tree) and `Provable k φ` (`Prop`, "∃ tree of size ≤ k"); `Pf` absorbed both,
and `legacy_iff_live` (`Research/Spikes/unified_pf/LegacyS.lean`) is the
meaning-preservation theorem. Older notes say `Provable k φ` — read it as `⊢_k φ`.

- `box` vs `Pf` feel similar (both "about provability of φ") but play opposite
  roles: `box k φ` is the *claim/name* (object-level syntax an agent can write
  and **nest**, e.g. `box j (box k φ)`); `Pf k φ` is the *evidence* (the
  derivation, built in Lean). Test: "can it be the subject of a `□`?" — `box`
  yes, `Pf` no (it isn't a `Formula`).
- `Pf k φ` is a **`Prop`** (a *claim*), so *writing* `⊢_k φ` does **not** make it
  hold — you need a proof term `h : Pf k φ`, and since `Pf` is an inductive such a
  term exists only if `S` genuinely derives φ. You can also state, and prove in
  Lean, `¬ Pf k φ` — "no `S`-derivation at budget `k` exists", the META fact
  `¬ ⊢_k φ`. That is the shape of every floor/exclusion census (`no_provable_*`).
  It is NOT `⊢_k ¬φ` (`S` *refutes* φ — the `atomNeg`/`eqNeg` route) and NOT
  "φ is false": `¬ ⊢_k φ` is compatible with `⊨ φ` (a true play below its floor).

## Meta-level vs object-level

The single most important distinction.

- **Object-level (inside `S`):** what the *agents* can express and derive. Their
  language is `Formula` (`plays`, `impl`, `neg`, `box`, `eq`, `diag`). "S proves
  φ" = `⊢_k φ` = `Pf k φ`. Provability here is **bounded** (budget `k`) and
  finitary.
- **Meta-level (Lean):** what *we* prove *about* the system. "φ is true" =
  `⊨ φ` = `φ.interp`. The bridge from object to meta is soundness,

  **`sound_upto : ⊢_k φ ⟹ ⊨ φ`** (`Base/Soundness.lean`; API form `Pf_sound`)

  — a Lean theorem ABOUT `S`, by strong induction on the budget (the `search_f`
  floor is what lets the induction go through). Löb forbids `S` from having
  `□_k φ → φ` uniformly; Lean can state and prove `⊢_k φ ⟹ ⊨ φ` because it sits
  outside `S`.

Provability (object) and truth (meta) are **different**: `⊢_k φ` = "S has a
(short) derivation"; `⊨ φ` = "φ holds of `eval`". Soundness goes one way
(`⊢_k φ ⟹ ⊨ φ`). The reverse (`⊨ φ ⟹ ⊢_k φ`) is *not* free — and it is no
longer assumed anywhere. The two former "kept axioms" that granted it in
restricted forms are gone:

- `atom_complete` (σ₁-completeness: true plays are derivable at *some* budget) —
  replaced by constructive certificate builders (`atom_complete_searchfree`,
  per-site `search_t`/`search_f` certificates). Still budget-sensitive: a true
  play can be `¬ ⊢_k` at too small a `k`; and the `search_f` FLOOR (an
  else-certificate costs more than the failed search it reports) makes some true
  plays `¬ ⊢_k` at the searcher's own budget for EVERY `k`. Its sibling
  `atom_complete_false_guard`, which handed those out cheaply, was machine-checked
  INCONSISTENT (T32, 2026-07-02) and deleted.
- `PBLT` (bounded Löb) — now the THEOREM `pblt_engine` (`Base/Loeb.lean`,
  with `bloeb_engine`): Lean builds the `S`-derivation explicitly through the
  internalized fixpoint sentence `Formula.diag` and the `diagF`/`diagB` rules.
  Still the one box-level principle driving the self-fulfilling bots
  (CUPOD/DUPOC self-play).

Why the reverse can never be a rule of `S`: it would require `S` to reflect on
its own provability — `□_k φ → φ` as an `S`-theorem — and Löb says `⊢ □_k φ → φ`
only when `⊢ φ` already. Reflection lives at the meta level only, as `sound_upto`.

### Quantifiers live at the meta-level

`Formula` is a **propositional, quantifier-free fragment** (deliberately — only
what the theorems need). It has *no* `∀`/`∃`. So every quantifier in our
statements (the `∃ m` budgets, the `∀ k` parameters) is a **Lean (meta)**
quantifier, *outside* `box`/`Pf`. Consequence for PBLT: Critch states
`⊢ (∀k)(…)` (□∀, quantifier *inside* the box); we can only write
`∀k, ⊢_{pm k} (…)` (∀□, quantifier *outside*), because `∀k, …` is not a
`Formula` and so cannot sit under a `box`. The ∀□ form is *weaker* but *sound*
(implied by Critch's lemma) and *sufficient* (proofs supply/consume
per-instance). Putting a quantifier *inside* the box would require adding
`∀`/`∃` constructors to `Formula` — i.e. internalizing the quantifiers — which we
chose not to do.

## Why making `S` explicit mattered

Originally `proofSearch` was a black-box `axiom` and `S` was ~12 axioms
*describing* it ("it's sound", "it reads source code", "it satisfies this
spec"). Once `S` became explicit — `proofSearch := decide ∘ Pf` over a
checkable inductive — those descriptions became **theorems** (you can *prove*
what you used to *assume* about a thing you now *build*). The trust base
collapsed first to three genuinely irreducible-looking assumptions
(σ₁-completeness, Löb, transport), then — bounded Löb internalized (2026-07-01),
the last atom axiom found inconsistent and replaced by the sound floor
(2026-07-03) — to nothing beyond Lean's own three. That collapse *is* the
separation of object-level (`S`) from meta-level (Lean): the oracle stopped
being an opaque assertion and became an object we reason about from outside.

## One-line glossary

- **Prog** — agent source code (L0).
- **Formula** — S's language; what agents reason in (L1, object-level syntax).
- **Pf k φ** — `⊢_k φ`: the `S`-derivation of φ within budget `k` (a `Prop`; a
  term of it is the proof tree; `box`'s meaning).
- **PlaysProof / AtomProvable** — the play-atom half of `Pf`: certificates that
  replay `eval` (`search_t`/`search_f` at the guards).
- **proofSearch k φ** — `Bool`: the oracle agents call (`decide ∘ Pf`).
- **box k φ** — `Formula`: the syntax `□_k φ` (name of provability, nestable).
- **interp** — `Formula → Prop`: `⊨ φ`, object-syntax ↦ meta-truth.
- **sound_upto / Pf_sound** — the bridge: `⊢_k φ ⟹ ⊨ φ` (a Lean theorem about S).
- **¬ ⊢_k φ** — no derivation at `k` exists (meta; the `no_provable_*` censuses);
  ≠ `⊢_k ¬φ` (S refutes φ) ≠ `¬ ⊨ φ` (φ false).
- **bloeb_engine / pblt_engine** — bounded Löb and PBLT as theorems (formerly the
  `PBLT` axiom).
- **decFull / evalG** — Lean-computable enumerator/evaluator (`Decidability/`):
  META objects that decide `⊢_k φ` — not part of `S`.

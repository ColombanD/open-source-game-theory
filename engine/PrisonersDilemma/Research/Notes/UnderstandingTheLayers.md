# Understanding the Layers

A short conceptual map of the engine: the layers it is built from, the objects
related to "proof", and the meta-level / object-level distinction. Written as a
study aid after the reform that made the proof system `S` explicit.

## The layers (bottom to top)

| Layer | What it is | Formal system | Key objects |
|---|---|---|---|
| **0. Programs** | the agents, as *source code* | none (it's syntax + an evaluator) | `Prog`; `eval`/`play`/`outcome` |
| **1. `S`** | the logic the *agents* reason in | the proof system `S` | `Formula`, `Derivation`, `Provable`, `proofSearch` |
| **2. Meta** | the logic *we* prove outcomes in | Lean / CIC | `theorem …`, `Formula.interp`, `Derivation.sound` |

- **Layer 0 — `Prog`.** Pure source code (Critch's Python-pseudocode bots). No
  constructor yields an `Action` directly; actions appear only by running code
  via `eval` (Dynamics.lean). Bots: `CupodBot`, `CIMCIC`, ….
- **Layer 1 — `S`, where the proof system lives.** When a bot does
  `.search k φ …` it asks an oracle to *prove a `Formula`*. `S` is the system
  that answers. **`S = (Derivation, Provable, proofSearch)`**, speaking the
  language `Formula`. This is the logic agents use to reason *about each other*.
- **Layer 2 — the meta-theory.** Lean itself. When we write
  `theorem CupodBot_vs_CupodBot …` we reason *about* layers 0 and 1. Its axioms
  are Lean's (`propext`, `Classical.choice`, `Quot.sound`).

**Where is `S`? Layer 1.** Not Lean (that's the meta-layer above it), not `Prog`
(those are the programs it reasons about). `S` sits *between*: agents (L0) call
`S` (L1) via `proofSearch`; we (L2) reason about `S` via `interp` + soundness.

## The objects linked to "proof" (one fact, four guises)

For a single fact "φ is provable within budget `k`":

| Object | Type | Role |
|---|---|---|
| `Derivation φ` | `Type` (data) | the **proof object** — an actual proof tree |
| `Provable k φ` | `Prop` | "a proof of size ≤ k **exists**" (∃ Derivation, or atom) |
| `proofSearch k φ` | `Bool` | the oracle's **yes/no**, `= decide (Provable k φ)` |
| `Formula.box k φ` | `Formula` | the **syntax** `□_k φ` inside S's language |

Chain: `Derivation` (the witness) → `Provable` (∃ witness ≤ budget) →
`proofSearch` (Bool reflection, what agents call) ; and `box` is the *syntactic
name* whose meaning (`interp`) **is** `Provable`.

- `box` vs `Derivation` feel similar (both "about provability of φ") but play
  opposite roles: `box k φ` is the *claim/name* (object-level syntax an agent
  can write and **nest**, e.g. `box j (box k φ)`); `Derivation φ` is the
  *evidence* (meta-level proof term we build). Test: "can it be the subject of a
  `□`?" — `box` yes, `Derivation` no (it isn't a `Formula`).
- `Provable` is a **`Prop`** (a *claim*), so *writing* `Provable k φ` does **not**
  make it true — you need a proof term `h : Provable k φ`. (You can also write,
  and sometimes prove, `¬ Provable k φ` — a failed search.) Contrast
  `Derivation φ`: to write a specific term you must *construct* it, and that
  construction *is* the proof, so a `Derivation` cannot exist for a false φ.

## Meta-level vs object-level

The single most important distinction.

- **Object-level (inside `S`):** what the *agents* can express and prove. Their
  language is `Formula` (`plays`, `impl`, `neg`, `box`). "S proves φ" =
  `Provable _ φ` / `∃ d : Derivation φ`. Provability here is **bounded** (budget
  `k`) and finitary.
- **Meta-level (Lean):** what *we* prove *about* the system. "φ is true" =
  `φ.interp`. The bridge from object to meta is
  **`Derivation.sound : Derivation φ → φ.interp`** ("provable ⟹ true") and its
  `Prop`-level form `Provable_sound`.

Provability (object) and truth (meta) are **different**: `Provable k φ` = "S has
a (small) proof"; `φ.interp` = "φ holds in the model". Soundness goes one way
(provable ⟹ true). The reverse (true ⟹ provable) is *not* free — it is exactly
what the kept axioms grant, and only in restricted forms:

- `atom_complete` — true atomic plays are provable (σ₁-completeness), but only at
  *some* budget (budget-sensitive; a true play can be unprovable within too
  small a `k`).
- `PBLT` — bounded Löb; the one box-level principle driving the self-fulfilling
  bots (CUPOD/DUPOC self-play).

Why the reverse can't be made constructive for the atoms: it would require S to
reflect on its own provability (`Provable → AtomProvable → guard □ → Provable`),
a genuine Löb/Gödel self-reference — so atom-provability stays opaque + axiomatic.

### Quantifiers live at the meta-level

`Formula` is a **propositional, quantifier-free fragment** (deliberately — only
what the theorems need). It has *no* `∀`/`∃`. So every quantifier in our
statements (the `∃ m` budgets, the `∀ k` parameters) is a **Lean (meta)**
quantifier, *outside* `box`/`Provable`. Consequence for PBLT: Critch states
`S ⊢ (∀k)(…)` (□∀, quantifier *inside* the box); we can only write
`∀k, (S ⊢ …)` (∀□, quantifier *outside*), because `∀k, …` is not a `Formula` and
so cannot sit under a `box`. The ∀□ form is *weaker* but *sound* (implied by
Critch's lemma) and *sufficient* (proofs supply/consume per-instance). Putting a
quantifier *inside* the box would require adding `∀`/`∃` constructors to
`Formula` — i.e. internalizing the quantifiers — which we chose not to do.

## Why making `S` explicit mattered

Originally `proofSearch` was a black-box `axiom` and `S` was ~12 axioms
*describing* it ("it's sound", "it reads source code", "it satisfies this
spec"). Once `S` became explicit — `proofSearch := decide ∘ Provable` over a
checkable `Derivation` type — those descriptions became **theorems** (you can
*prove* what you used to *assume* about a thing you now *build*). The trust base
collapsed to the genuinely irreducible assumptions (σ₁-completeness, Löb,
transport). That collapse *is* the separation of object-level (`S`) from
meta-level (Lean): the oracle stopped being an opaque assertion and became an
object we reason about from outside.

## One-line glossary

- **Prog** — agent source code (L0).
- **Formula** — S's language; what agents reason in (L1, object-level syntax).
- **Derivation** — a proof object in S (the witness).
- **Provable k φ** — `Prop`: a size-≤k proof exists (box's meaning).
- **proofSearch k φ** — `Bool`: the oracle agents call (`decide ∘ Provable`).
- **box k φ** — `Formula`: the syntax `□_k φ` (name of provability, nestable).
- **interp** — `Formula → Prop`: object-syntax ↦ meta-truth.
- **Derivation.sound** — the bridge: provable ⟹ true.

# Provability notation — `⊢`, `⊨`, and the meta level

*Fixed 2026-09-04. The convention every comment, note, prompt and paper section
follows when it talks about "proving". Companion to `UnderstandingTheLayers.md`.*

## The three levels, the three notations

| Level | Notation | Engine object | Read as |
|---|---|---|---|
| **Object provability** (`S`) | `⊢_k φ` | `Pf k φ` | `S` derives `φ` with a transcript of length ≤ `k` |
| **Truth** (a Lean proposition) | `⊨ φ` | `φ.interp` | `φ` holds of the real evaluator |
| **Meta** (Lean itself) | prose only | `theorem …` | *we* show / Lean verifies |

- `⊢` **always** refers to `S`, never to Lean. `S ⊢_k φ` is acceptable but the
  prefix is redundant; `Lean ⊢` is never written. Unsubscripted `⊢ φ` abbreviates
  `∃ k, ⊢_k φ`; state the budget whenever a nearby theorem does.
- `⊨ φ` is the Lean proposition `φ.interp`, e.g.
  `⊨ (p plays a vs q)  =  ∃ n, play n p q = some a`.
- The meta level has **no symbol**. "Lean proves", "we show", "theorem",
  "machine-checked" are the meta words. A turnstile in prose is always `S`.
- Inside `S`'s own language, `□_k φ` is the *syntax* `Formula.box k φ`: `S`'s name
  for its own provability, an object a bot can write and nest. It is not a claim.

The one identity that ties them, by definition of `interp` on `.box`:

```
⊨ □_k φ   ≡   ⊢_k φ          ("the box is true"  =  "S proves it at k")
```

Every quantifier (`∀ k`, `∃ m`, the thresholds `k₂`) is a **meta** quantifier:
`Formula` has no quantifiers, so nothing binds under a `□`.

## The standard theorems in this notation

| Name | Statement | Level of the proof |
|---|---|---|
| soundness `sound_upto` | `⊢_k φ  ⟹  ⊨ φ` | Lean, about `S`. Löb says `S` cannot have `⊢ □_k φ → φ` uniformly; Lean can, because it sits outside `S`. |
| guard fires `proofSearch_spec` | `proofSearch k φ = true  ⟺  ⊢_k φ  ⟺  ⊨ □_k φ` | definition |
| necessitation `boxIntro` | `⊢_k φ  ⟹  ⊢_{k'} □_k φ` for `k'` ≥ the transcript | a rule of `S` |
| bounded Löb `bloeb_engine` | `⊢_{pm} (□_{fb} φ → φ)`, headroom `pm ≺ fb`  ⟹  `⊢_m φ` | Lean builds the `S`-derivation explicitly |
| PBLT `pblt_engine` | `∀ k > k₁. ⊢_{pm k} (□_{f k} φ_k → φ_k)`, headroom  ⟹  `∃ k₂. ∀ k > k₂. ∃ m. ⊢_m φ_k` | same, one derivation per `k` |
| an outcome theorem | `outcome k L R = some (a, b)` | meta: a Lean statement about `eval`, proved through `⊢` (the guards fire) and `⊨` (soundness turns firing into plays) |

Critch's premise is one `S`-proof with `k` quantified *inside* `S`; ours is a
Lean-indexed schema of per-`k` `S`-proofs at budget `pm k = O(log k)`. His implies
ours (instantiating the numeral costs its digits), which is why consumers supply a
single-leaf premise and why `pm` must never be weakened up to `f`.

## Three negations that are not the same thing

| Written | Meaning | Where it appears |
|---|---|---|
| `¬ ⊢_k φ` | no `S`-derivation of `φ` at budget `k` exists — a **meta** fact | the floor/exclusion censuses (`no_provable_*`), a guard that does not fire |
| `⊢_k ¬φ` | `S` **refutes** `φ` — an object derivation | `atomNeg`, `eqNeg`, the `search_f` else-certificate suppliers |
| `⊢_{k'} ¬□_k φ` | `S` proves its own unprovability of `φ` at `k` — internal, and Löb-constrained | what the deleted axiom faked; see `DESIGN_CHOICES.md` §"anti-diagonal" |

"Unprovable" in prose means the first row unless said otherwise. It never means
"false": `¬ ⊢_k φ` is compatible with `⊨ φ` (a true play below its floor).

## Words to avoid, and what to write instead

| Ambiguous | Write |
|---|---|
| "φ is provable" | `⊢_k φ` / "`S` derives φ at `k`", or "a Lean theorem" — say which |
| "φ is true" / "holds" | `⊨ φ` when the object is a `Formula`; plain prose for meta facts |
| "the proof of φ" | "the `S`-derivation" (a `Pf` term) vs "the Lean proof" (of a `theorem`) |
| "certificate" | a `Pf`/`PlaysProof` term — object level |
| "Lean proves `S ⊢ φ`" | fine, and exactly what a lemma `… : Pf k φ` is |

## In Lean source

In tactic blocks `⊢` is Lean's **goal marker** (`simp at h ⊢`) and is untouched by
this convention. In comments and docstrings `⊢` always means `S`; a comment that
describes a Lean goal writes `goal:` instead of a turnstile, so `-- goal: Pf k φ`
never reads as `S` proving `Pf`. The hypothesis annotations in the Löb chains
(`-- s₁ : ⊢ □_fb C → …`) are `Pf` terms and already follow the convention.

## Relation to Critch 2022

| Role | Critch | Here |
|---|---|---|
| object system the agents reason in | PA, or any `S ⊇ PA` | `Pf` (bounded GL directly, `Base/BoundedGL.lean` is the interface) |
| meta-theory | ZFC, informal | Lean's CIC, checked |
| the box | PA's provability predicate | `Formula.box`, interpreted as `Pf` |

The arithmetized model, where `□` is a genuine provability predicate over PA, is
the stated unfilled obligation of `BoundedGL`; our `S` is the modal system itself.

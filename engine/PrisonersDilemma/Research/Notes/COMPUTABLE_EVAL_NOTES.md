# Computable `eval`: the boundary

_Paper-section source material. The central evaluator `eval` is `noncomputable`; a
review flagged this. This document is the settled answer, structured the way the paper
section should run: the claim, why the limit is **fundamental to the theory** (not our
implementation), the artifact that exhibits the boundary, and what is safe to quote._

_Status: build green; no `sorry`; 4 axioms. All claims below are backed by checked Lean._

---


## 0. Colomban's Writing
Below is an LLM generated summary of why no computable eval is possible right now, but the main things to remember are the following:

- First, Critch fundamentally changes the PA, PA+1, ... tower of Barasz by making its agents computable using proof length. It removes the problem of Pi_1 undecidibility, because everything has a fixed proof length and thus everything is decidable.
- Theoretically, suppose we build S completely from the ground up. We prove the Löb Thm and all our axioms, so everything is constructive. Then in this case, we could create a computable eval.
- The problem is that we have these theorems as axioms, and so they are kinda non-computable by nature, so eval has to be non computable.



## 1. The claim

`eval` (and hence `play`/`outcome`) is `noncomputable` **as the development currently
stands**, and cannot be made totally computable *while the reflection principles are
kept as witness-free axioms*. That qualifier is the whole point: the limit is **relative
to our axioms, not absolute** — it is **not** a Gödel/Π₁ wall (§2b shows how it lifts).

The crucial distinction is between two predicates:

- **`Provable_finite k φ`** — "there is a finite proof *term* of size ≤ k." This is
  **decidable**: enumerate the finitely many proofs of size ≤ k and check. Bounding `k`
  is exactly what makes this finite. (This is the sense in which Critch's bounded `□_k`
  is built to be computable — it collapses Barász's PA, PA+1, … tower, whose unbounded
  provability is RE-but-not-recursive, into a fixed-length, decidable check.)
- **`Provable k φ`** — our *actual* Lean predicate. It is `Provable_finite` **plus members
  injected by the reflection axioms** (`PBLT`, `atom_box_provable_impl`). Those axioms
  assert `Provable k φ` for the Löb-fixpoint outcomes *without supplying a proof term* —
  an IOU, not a witness.

`decide (Provable k φ)` is noncomputable today because it would have to return `true` on
the axiom-injected members, which have **nothing to enumerate**. So — contrary to an
earlier draft of this note — the obstruction is **not** undecidability of bounded
provability (that predicate is decidable). It is that *our* `Provable` smuggles in
witness-free postulates.

What we ship today: a **sound, total, computable _partial_ evaluator** `evalC` that
agrees with `eval` wherever it commits and abstains (`none`) exactly at the Löb
fixpoints. The evaluator's only non-constructive ingredient is its `.search`-guard
oracle:

```
eval … (.search k φ p q) … = if proofSearch k (φ.subst me opp) then run p else run q
proofSearch k φ := decide (Provable k φ)        -- classical, hence noncomputable
```

So "make `eval` computable" = "compute `proofSearch` = decide our `Provable`", which is
exactly what the witness-free axioms block.

## 2. Why it is blocked *today*, and how the block lifts

### 2a. The semantic core — axioms are IOUs the evaluator cannot cash

A running evaluator must decide each `.search` guard *by computing a Bool* — i.e. by
*searching* proof-space and either finding a witness (`true`) or exhausting the bounded
space (`false`). An **axiom contributes no searchable object**: `axiom PBLT : … Provable
k φ` says the Prop is inhabited but hands over no term to find. So on the Löb-fixpoint
outcomes — canonically `outcome_PrudentBot_vs_DupocBot = (C,C)`, established *through*
`PBLT`/`atom_box_provable_impl` and reflected into the oracle via `proofSearch_spec.2`
(`Provable → proofSearch = true`) — a sound bounded search finds nothing and returns
`false`/undecided, **contradicting** the axiom's `true`. No computable function can
satisfy the present `proofSearch_spec`.

This is *not* "no proof can exist." The Löb proof, **if constructed**, is itself a finite
bounded proof term (Löb's theorem is *why* a sound such proof exists). We merely
postulated it instead of building it. Cash vs. IOU — and the evaluator needs cash.

### 2b. How the block lifts — fully explicit `S`

Replace each reflection axiom with a **constructive** theorem that actually exhibits (or
constructively proves the existence of) a size-≤-`k` proof term — i.e. mechanize bounded
provability logic and a **constructive (parametric) bounded Löb theorem** (`PBLT`). Then
`Provable k φ` collapses to `Provable_finite k φ` (every member has a finite witness),
which is decidable by enumeration. Consequences:

| | today (axioms) | fully explicit `S` |
|---|---|---|
| `Provable_finite k φ` decidable | yes | yes |
| our `Provable k φ` decidable | **no** (witness-free members) | **yes** |
| `eval` computable | no | **yes**, Löb fixpoints included |
| project axioms | 4 | the 3 Lean-standard ones |

So a *totally* computable `eval` is reachable — it is **finite, ordinary metamathematics**
(constructive bounded Löb + HBL conditions), with **no undecidability wall**, precisely
because the bounded regime is where Gödel does not bite. Hard formalization work, not an
impossibility.

> Decision-procedure note: with explicit `S` one decides `Provable k φ` by **enumerating
> proof terms of size ≤ k** (the `Provable_finite` route — trivially terminating over a
> finite set), *not* by structural recursion on the program. That sidesteps the
> obstruction of §2c entirely — §2c only refutes the *structural-recursion* approach.

### 2c. A refuted shortcut — no naive structural measure (machine-checked)

`ComputableEval/DecMeasure.lean`. One *might* try to decide `Provable k φ` by structural
recursion through the `search_t` guard `Provable kg (ψ.subst me opp)`, with measure
`(k, search-nesting-depth)` — `kg` a source literal (≤ `2^k`, not `< k`), `ψ` substituted
with the players. That measure is **false**, by `decide`:

```
meP := .search 0 (.eq .self .self) .self .self        -- searchDepth = 1
(guard of meP).subst meP meP   has searchDepth = 2     -- self-substitution RAISES depth
```

Substituting a `.search`-bot into its own guard *increases* search-depth (the Löb
self-reference), so the natural structural recursion does not bottom out. This refutes the
*recurse-on-the-program* strategy (it is what sank our own `derivable`/`Decidable`-instance
attempts); it does **not** contradict §2b, which decides by enumerating proof *terms*.

**Conclusion.** Total computability is blocked *only* by keeping reflection as witness-free
axioms. Until that foundational work (§2b) is done, `eval` stays classical and we ship the
sound *partial* `evalC` (§3). The "wall" is an IOU we have not yet cashed — not a Gödelian
impossibility.

## 3. The boundary, exhibited — `evalC` (the figure)

`ComputableEval/Computable.lean` + `Demo.lean`. We make the boundary **constructively
locatable** with a runnable evaluator. This is an illustration, not the proof of §2 —
its value is that it pins down *where* bounded computation stops, with a machine-checked
guarantee that it never lies up to that point.

**Design — a 3-valued guard.** `decGuard : Nat → Nat → Formula → Option Bool` returns
- `some true`  — a finite play witness exists and fits the node budget `k` ⇒ run the then-branch;
- `some false` — a finite refutation (the subject provably plays another action) ⇒ run the else-branch;
- `none`       — undecided within fuel (a Löb fixpoint) ⇒ `evalC` returns `none`.

`evalC`/`playC`/`outcomeC` thread `none` through. (A first *2-valued* attempt was
**unsound**: it silently took the else-branch on undecided guards, returning the wrong
action where the real bot cooperates — `decGuard` fired `true`/`false` where neither
holds. The 3-valued, budget-aware design is what fixes this; the cliff edge is real and
narrow.)

**Faithfulness is proved, not asserted.** `evalC_eq_and_decGuard_sound` (strong
induction on fuel) yields `evalC_sound` / `playC_sound` / `outcomeC_sound`: **every**
`some _` that `evalC` returns equals the classical `eval`/`outcome`. So the `#eval`
outputs are theorems, not coincidences.

**The boundary, by example** (from `Demo.lean`, all checked):

```
#eval outcomeC 50 CooperateBot DefectBot          -- some (C, D)
#eval outcomeC 10 (DupocBot 100) CooperateBot      -- some (C, C)   — a real .search guard firing
#eval outcomeC  8 (PrudentBot 100) (DupocBot 100)  -- none          — the Löb fixpoint
```

That last `none` is the figure's punchline: `outcomeC` refuses *exactly* at the modal
fixpoint rather than guessing. The cooperative `(C,C)` there is the **theorem**
`outcome_PrudentBot_vs_DupocBot`, established via the reflection *axioms* — and that is
the whole point: `evalC` returns `none` there precisely because the witness was
postulated, not built. The boundary `evalC` draws is the line of *our current axioms*,
which §2b says is movable, not an absolute frontier of computation.

## 4. What this answers, and what to quote

- It answers the review point **honestly and without over-claiming**: noncomputability
  today is not sloppiness — it is forced *by our choice to keep reflection as axioms*
  (§2a) — and we exhibit the precise locus with `evalC` (§3). We are careful NOT to call
  it a fundamental/Gödel limit: §2b shows it lifts once `S` is made fully explicit
  (constructive bounded Löb), after which a *total* computable `eval` is reachable.
- It also addresses the "too many axioms" point, which is the *same* lever: during this
  work `c_guard_mono` was demoted from axiom to **theorem** (4 axioms remain: `PBLT`,
  `box_provable`, `atom_box_provable_impl`, `atom_complete_false_guard`). Discharging
  these reflection primitives constructively is exactly what would *both* shrink the axiom
  count toward the 3 Lean-standard ones *and* make `eval` computable — one piece of
  foundational work, two payoffs.
- **`atom_complete_false_guard` is the nearest win**: it is atom-layer and bounded, with
  no reflection self-reference, so its false-guard certificate should be *constructively
  derivable by enumeration* — a theorem, not an axiom. Worth a focused, separate task.

Suggested framing for the paper:

> The evaluator's `.search` guard is a bounded-provability oracle. We do not yet decide
> it computably: the cooperative Löb-fixpoint outcomes are reflected through the oracle's
> specification via *axioms* (`PBLT`, `atom_box_provable_impl`) that assert provability
> without exhibiting a bounded proof term, so a terminating search finds no witness. This
> is a limitation of the *current axiomatization*, not of bounded provability itself —
> which is decidable by enumeration. We therefore retain a classical `eval` and supply a
> separate, sound, computable *partial* evaluator `evalC`, proven equal to `eval`
> wherever it commits and returning `none` exactly at the as-yet-unconstructed fixpoints.
> Mechanizing a constructive bounded Löb theorem would discharge those axioms and make
> `eval` totally computable — future work.

**Quote-safe facts:** build green, 0 `sorry`, 4 axioms; `outcomeC_sound` (and its `eval`
/ `play` siblings) is fully proved; the `DecMeasure` counterexample is `decide`-checked;
the `none` at `PrudentBot × DupocBot` is reproducible via `#eval`.

**Do NOT claim:** that `evalC` is total, that it decides the fixpoints, that bounded
provability is undecidable, or that the noncomputability is a Gödel/fundamental wall (it
is axiom-relative — §2b). `DecMeasure` only refutes the *structural-recursion* shortcut
(§2c), not decidability per se.

---

## Roadmap to fully-explicit `S` (removing all 4 axioms) — corrected ordering

What "make `S` completely explicit" decomposes into, and the dependency order between
the phases. **The key correction (2026-06-23):** the naive intuition is "decide
`Provable` first, then constructive Löb falls out." That is BACKWARDS, and `DecMeasure`
+ `Computable` prove why. Deciding `Provable` by enumeration is only *coherent* AFTER the
witness-free axioms (PBLT, the removed `atom_box_provable_impl`) are replaced by
constructive rules that inject finite proof TERMS — i.e. after constructive Löb. So
constructive bounded Löb (Phase 4), not decidability (Phase 2), is the true keystone.

### The single foundational move

Size-index `Derivation` (`Derivation : Nat → Formula → Type`, size in the index, not the
post-hoc conclusion-measure it is today) so that `Provable k φ` can collapse to a
DECIDABLE, finite, enumerate-the-proof-terms predicate. Every axiom-removal below is a
consequence of this move.

### Dependency graph (corrected order: 0 → 1 → 4 → 2 → 3)

```
Phase 0  size-index Derivation  (Derivation : Nat → Formula → Type)
   │      the enabling refactor; real structural size, not `| φ, _ => φ.size`
   │
   ├──► Phase 1  boxIntro constructor ───────────► KILLS `box_provable`
   │      bounded GL-4 / necessitation made constructive; needs Phase 0's size index
   │      for the `K ≤ (.box k φ).size` bound the axiom currently asserts.
   │
   └──► Phase 4  constructive bounded Löb ───────► KILLS `PBLT`   ◄── TRUE KEYSTONE
            │    mechanize critch22 Lemma 3.6: from S ⊢ □_{f(k)}φ(k) → φ(k), BUILD a
            │    size-≤-f(k) derivation of φ(k). Research-level: needs a Formula/Derivation
            │    representation of the diagonal fixpoint + size arithmetic. This is what
            │    gives the Löb fixpoints (PrudentBot↔DupocBot) a FINITE PROOF TERM —
            │    the thing they lack today (Computable.lean: "no finite play witness").
            │    Also closes the `sorry`'d Löb matchups (Axioms.lean §REMOVED).
            │
            └──► Phase 2  Decidable (Provable k φ) ─► proofSearch/eval COMPUTABLE
                     │    NOT doable before Phase 4 — over TODAY's `Provable` it is
                     │    machine-checked-impossible (witness-free fixpoints have no
                     │    `true`-returning computation; DecMeasure refutes the structural
                     │    route, Computable explains the reflection reason). AFTER Phase 4
                     │    every member has a bounded witness ⇒ "enumerate proof terms of
                     │    size ≤ k" terminates. Remaining work = a verified Fintype/
                     │    enumerator over the size-indexed mutual inductive + checker
                     │    completeness (moderate-hard engineering, no known obstruction).
                     │    Drops `noncomputable` from proofSearch; concrete outcomes → `by decide`.
                     │
                     └──► Phase 3  search_f constructor ─► KILLS `atom_complete_false_guard`
                              once `Provable k φ` is decidable its NEGATION is too, so the
                              Π₁ false-guard residue becomes a positive constructor
                              (`¬ Provable k guard → … → PlaysProof … (.search …)`).
                              Easy GIVEN Phase 2.
```

### Difficulty / axiom scorecard

| Axiom | Removed by | Difficulty |
|---|---|---|
| `box_provable` | Phase 1 (boxIntro) | moderate |
| `PBLT` | **Phase 4 (constructive Löb)** | **hard / research — the linchpin** |
| `atom_complete_false_guard` | Phase 3 (search_f) | easy *given Phase 2* |
| *(decidability prereq)* | Phase 2 (enumerate bounded proof terms) | moderate-hard *given Phase 4* |

End state: `Axioms.lean` → empty (just Lean's `propext`/`Classical.choice`/`Quot.sound`);
`eval` total & computable; concrete fixed-`(k,fuel)` outcomes by `decide`; ∀k-family
theorems lean on a *proved* Löb. The whole project's noncomputability is then discharged,
confirming §2b: axiom-relative, not a Gödel wall.

### Why the existing computable-eval work matters here

It gives no head start on the *positive* enumerator, but three things: (1) a machine-checked
proof that the naive structural-recursion route is a dead end (`DecMeasure`, §2c) — don't
retry it; (2) the exact diagnosis that the blocker is witness-free AXIOMS, which is *why*
Phase 4 is the unlock and Phase 2 cannot precede it; (3) `evalC` as a proven-sound fallback
/ ceiling if Phase 4 resists — correct wherever it commits, `none` exactly at the fixpoints.

---

## Provenance (not for the paper)

This file supersedes a chronological investigation log. Two total-computability routes
were tried and abandoned **for the axiomatized `S` we have today** (NOT in principle):
a separate-search-gas `derivable` checker (non-monotone: conflated "not found yet" with
"unprovable"), and a `Decidable (Provable k φ)` instance by structural recursion on the
program (refuted by `DecMeasure.lean`, §2c). Both fail only because the reflection axioms
inject witness-free members into `Provable`; the principled route to *total*
computability is §2b (constructive bounded Löb + enumerate proof terms of size ≤ k),
which is unimplemented foundational work, not a dead end.

The shipped result is the sound partial `evalC`: keep classical `eval`, exhibit the
boundary. Artifacts in `engine/PrisonersDilemma/ComputableEval/` (`Computable.lean`,
`Demo.lean`, `DecMeasure.lean`); `c_guard_mono` is now a theorem in `Axioms.lean`.

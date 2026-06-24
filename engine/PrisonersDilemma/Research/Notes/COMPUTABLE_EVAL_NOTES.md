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
- Theoretically, suppose we build S completely from the ground up. We prove the Löb Thm and all our axioms, so everything is constructive. Then in this case, we could create a computable eval. Actually no, that is not the case (see bellow).
- The problem is that we have these theorems as axioms, and so they are kinda non-computable by nature, so eval has to be non computable.

> ⚠️ **Bullet 2 is now known to be too optimistic (correction 2026-06-23).** "Build S from
> the ground up, prove Löb constructively ⇒ computable eval" does NOT hold at the Löb
> fixpoints. Proving Löb (even constructively, the Critch way) gives an *existence*
> statement `∃ proof`, not an extractable proof *term* — and eval's guard needs the term.
> A *term-builder* Löb would suffice but is refuted for this engine (spikes S3/S3′,
> `CONSTRUCTIVE_BOUNDED_LOB.md`). So: explicit S shrinks the axioms but eval stays
> noncomputable AT THE FIXPOINTS (computable everywhere else, already, via `evalC`). See the
> corrected §1, §2a (⚠️ proof-vs-witness), §2b, and the roadmap scope box below.



## 1. The claim

`eval` (and hence `play`/`outcome`) is `noncomputable`. **The honest, corrected claim
(2026-06-23):** it is computable on the **finite fragment** (every non-self-referential
matchup — `evalC` commits there, proven sound), but **NOT** at the cooperative **Löb
fixpoints**, and that block is **not lifted by making `S` explicit**. The limit is **not** a
Gödel/Π₁ wall (the finite fragment is genuinely decidable) — but it is also **not** the
purely "axiom-relative, just-go-build-it" limit an earlier draft of this note claimed.
The fixpoint block is the **proof-vs-witness gap** (§2a ⚠️): a proof of bounded Löb yields
`∃ m, Provable m φ` (existence), never an extractable proof *term* (witness), and `eval`'s
guard needs the term. Spikes S3/S3′ (`CONSTRUCTIVE_BOUNDED_LOB.md`) machine-check that the
witness route is blocked for this engine.

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

> ⚠️ **CORRECTION (2026-06-23) — "a proof of Löb" is NOT "a witness".** The paragraph
> above (and §2b below) blurs a distinction that turns out to be decisive. There are two
> different objects both called "the Löb proof":
> - **(i) an *existence* claim** — `∃ m, Provable m φ`, i.e. "a size-bounded proof of the
>   fixpoint atom exists." This is what classical Löb / Critch's PBLT (`PBLT_proof.tex`)
>   delivers. Its argument goes through the **diagonal lemma**: it constructs the
>   self-referential *formula* ψ and reasons *about the existence* of proofs — it **never
>   exhibits a derivation tree.**
> - **(ii) a *witness*** — a computable function returning the actual size-≤-`k` proof
>   *term*, in `Type`, which `decide`/enumeration can produce.
>
> **`eval` needs (ii). Classical/faithful Löb only gives (i). And (i) does NOT yield (ii).**
> So replacing the `PBLT` *axiom* with a *theorem* proved Critch-style hands you another
> existential — `decide` still has nothing to enumerate to, `eval` stays noncomputable.
> **Discharging the axiom changes the axiom count, NOT computability.** The only thing that
> would help is a *term-builder* form of bounded Löb (ii) — and that is refuted for this
> engine by spike **S3′** (`Research/Notes/CONSTRUCTIVE_BOUNDED_LOB.md`, `PD.SpikeS3prime`):
> the witness it would have to produce is `Provable k φ` at the **same** budget `k` (the
> bot searches at its own `k`; `eval`'s `.search` rule, machine-checked by `rfl`), the
> self-referential atom — and the diagonal lemma, the only known route to (i), does **not**
> factor through a size-decreasing term construction. **Both roads are blocked:** (i) gives
> the wrong kind of object, (ii) cannot be built. See the corrected §2b.

### 2b. How the block lifts — fully explicit `S` _(CORRECTED 2026-06-23 — see ⚠️)_

The original claim here was: *replace each reflection axiom with a constructive theorem
exhibiting a size-≤-`k` proof term; then `Provable` collapses to the decidable
`Provable_finite`, and `eval` becomes computable, Löb fixpoints included.* **The Löb-fixpoint
half of that is now believed FALSE** — for the precise reason in the ⚠️ box of §2a (proof ≠
witness) and the machine-checked spikes S3/S3′ (`CONSTRUCTIVE_BOUNDED_LOB.md`).

What survives, and what doesn't:

| | today (axioms) | fully explicit `S` |
|---|---|---|
| `Provable_finite k φ` decidable | yes | yes |
| our `Provable k φ` decidable **on the finite fragment** (non-fixpoint matchups) | effectively yes (`evalC` commits) | yes |
| our `Provable k φ` decidable **at the Löb fixpoints** | no | **STILL NO** — corrected ✗ |
| `eval` computable **off the fixpoints** | already (`evalC`) | yes |
| `eval` computable **at the fixpoints** | no | **STILL NO** — corrected ✗ |
| `box_provable`, `atom_complete_false_guard` removable | — | **yes** (Phases 1, 3 — genuine wins) |
| `PBLT` removable as an *axiom* (→ existence *theorem*) | — | yes, but **does not buy computability** |

**Why the fixpoint cells are corrected to ✗.** Making `S` explicit lets you *prove* the
fixpoint atom is provable — but only as an **existence statement** `∃ m, Provable m φ`
(form (i), §2a), because the only known proof of bounded Löb is Critch's **diagonal-lemma**
argument, which reasons about the existence of proofs and never builds a derivation tree. To
make `eval` compute the `.search` guard you need form (ii): a **witness** — a computable
function returning the size-≤-`k` proof *term*. (i) does not yield (ii). The term-builder
route (ii) — `boundedLob`, recursion on budget — is **refuted by S3′**: the witness it must
return is `Provable k φ` at the *same* budget `k` (the bot searches at its own `k`; verified
by `rfl`), the self-referential atom, and the diagonal lemma does not factor through a
size-decreasing term construction.

So: explicit `S` **shrinks the axiom count** (removing `box_provable`,
`atom_complete_false_guard`, and demoting `PBLT` to a theorem) — a real, worthwhile result —
but it does **NOT** make `eval` totally computable. The Löb fixpoints stay noncomputable
**because a proof of Löb is not a witness**, not because of any Gödel wall. `evalC`'s `none`
at the fixpoints is therefore the *honest, permanent* boundary of the bounded-search regime,
not a temporary artifact of unfinished work.

> **Net:** the noncomputability is still **not a Gödel/Π₁ wall** (the *finite fragment* is
> genuinely decidable), but it is **also not "axiom-relative and liftable"** in the way this
> section originally claimed. It is liftable for the NON-fixpoint fragment (already is, via
> `evalC`); at the fixpoints it is blocked by the proof-vs-witness gap, which explicit `S`
> does not close. The accurate one-liner: *the Löb fixpoints are exactly where bounded
> provability has a proof of provability but no extractable proof term, so they are decidable
> in classical existence but not by computation.*

> Decision-procedure note: one decides **`Provable_finite k φ`** by **enumerating proof
> terms of size ≤ k** (trivially terminating over a finite set), *not* by structural
> recursion on the program — that sidesteps §2c entirely. **But careful (corrected):** this
> decides `Provable_finite`, which equals our `Provable` **only off the Löb fixpoints**. At
> a fixpoint the cooperation has no size-≤-k proof *term* to enumerate to (its only "proof"
> is the existence statement form (i), §2a) — so enumeration correctly returns `false`/finds
> nothing there, and that is *not* a decision of the fixpoint's actual (axiom-asserted)
> membership in `Provable`. Enumeration decides the finite fragment; it does **not** decide
> `Provable` at the fixpoints, and explicit `S` does not change this.

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

**Conclusion (corrected 2026-06-23).** This section refutes the *recurse-on-the-program*
shortcut to deciding `Provable`. It does **not** establish that total computability is
"just unfinished work." On the **finite fragment** `eval` is computable (enumerate proof
terms; `evalC` does this). At the **Löb fixpoints** it is blocked — and that block is **not**
merely "an IOU not yet cashed." The IOU framing was the error: cashing it (proving Löb,
even constructively) buys an *existence* statement, not the proof *term* `eval` needs (§2a
⚠️). So `eval` stays classical, we ship the sound *partial* `evalC` (§3), and the `none` it
returns at the fixpoints is the **honest, permanent** edge of the bounded-search regime —
not a Gödelian impossibility (the finite fragment is decidable), but not removable by making
`S` explicit either.

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
- It also addresses the "too many axioms" point — but this is **NOT** the same lever as
  computability (corrected 2026-06-23; the original claim of "one piece of work, two
  payoffs" was wrong). During this work `c_guard_mono` was demoted from axiom to
  **theorem** (4 axioms remain: `PBLT`, `box_provable`, `atom_box_provable_impl`,
  `atom_complete_false_guard`). Discharging `box_provable` and `atom_complete_false_guard`
  constructively shrinks the axiom count toward the 3 Lean-standard ones — a real payoff.
  But discharging `PBLT` (even constructively, Critch-style) yields an **existence**
  theorem `∃ m, Provable m φ`, not a **witness**, so it does **not** make `eval` computable
  at the fixpoints (§2a ⚠️, §2b). Axiom-shrinking and fixpoint-computability are
  **separate** outcomes; the latter is blocked by the proof-vs-witness gap regardless.
- **`atom_complete_false_guard` is the nearest win**: it is atom-layer and bounded, with
  no reflection self-reference, so its false-guard certificate should be *constructively
  derivable by enumeration* — a theorem, not an axiom. Worth a focused, separate task.

Suggested framing for the paper:

> The evaluator's `.search` guard is a bounded-provability oracle. On the finite fragment —
> every matchup that is not a Löb self-reference — it is decidable by enumerating proof
> terms of size ≤ k, and our sound computable *partial* evaluator `evalC` commits there,
> proven equal to the classical `eval`. At the cooperative **Löb fixpoints** it returns
> `none`: these outcomes are reflected through the oracle's specification via *axioms*
> (`PBLT`, `atom_box_provable_impl`) that assert *provability* without exhibiting a proof
> *term*. Critically, this is **not** merely an artifact of using axioms — a proof of
> bounded Löb (classical or constructive, à la Critch's diagonal lemma) establishes that a
> bounded proof *exists* (`∃ m, Provable m φ`) but does **not** yield an extractable proof
> *term*, which is what a terminating guard search would need. We prove this boundary is
> real: in the present engine the fixpoint's required witness is `Provable k φ` at the same
> budget `k` the bot searches (machine-checked), so no budget-decreasing construction
> produces it. Thus the Löb fixpoints are exactly where bounded provability has a *proof of
> provability* but no *computable witness* — decidable in classical existence, not by
> computation. The noncomputability is therefore **not a Gödel/Π₁ wall** (the finite
> fragment is genuinely decidable) but also **not liftable** by making `S` explicit: explicit
> `S` shrinks the axiom count, it does not close the proof-vs-witness gap at the fixpoints.

**Quote-safe facts:** build green, 0 `sorry`, 4 axioms; `outcomeC_sound` (and its `eval`
/ `play` siblings) is fully proved; the `DecMeasure` counterexample is `decide`-checked;
the `none` at `PrudentBot × DupocBot` is reproducible via `#eval`.

**Do NOT claim:** that `evalC` is total; that it decides the fixpoints; that bounded
provability is undecidable (the *finite fragment* is decidable); that the noncomputability
is a Gödel/fundamental wall; **or — corrected — that making `S` explicit / discharging the
axioms would make `eval` totally computable.** It would not: a (constructive) proof of
bounded Löb gives an existence statement, not the extractable proof *term* the guard needs
(§2a ⚠️, §2b), and S3′ machine-checks that the term route is blocked for this engine. The
defensible claim is the proof-vs-witness one: *the Löb fixpoints have a proof of provability
but no computable witness.* `DecMeasure` refutes the *structural-recursion* shortcut (§2c);
S3/S3′ (`CONSTRUCTIVE_BOUNDED_LOB.md`) refute the *budget-recursion / term-builder* route.

---

## Roadmap to fully-explicit `S` (removing all 4 axioms) — corrected ordering

> ⚠️ **SCOPE (corrected 2026-06-23).** This roadmap is about **removing axioms** (making `S`
> explicit), which is a worthwhile goal in its own right. It is **NOT** a roadmap to a totally
> computable `eval`. Earlier this file conflated the two ("one move, two payoffs"); the spikes
> S3/S3′ (`CONSTRUCTIVE_BOUNDED_LOB.md`) show they come apart. Reading guide for the phases
> below: **Phases 1 & 3 are genuine** (they remove `box_provable` and
> `atom_complete_false_guard` by exhibiting real certificates). **Phase 4 removes `PBLT` only
> as an *existence theorem*** — it does NOT yield a proof *term* for the fixpoint, so the
> "Phase 2 ⇒ eval computable at the fixpoints" arrow is **FALSE** and struck through below.
> Phase 2's enumeration decides `Provable_finite` (= `Provable` off the fixpoints) — that part
> is real; it just does not extend through the fixpoints.

What "make `S` completely explicit" decomposes into, and the dependency order between
the phases. **The key correction (2026-06-23):** the naive intuition is "decide
`Provable` first, then constructive Löb falls out." That is BACKWARDS, and `DecMeasure`
+ `Computable` prove why. Deciding `Provable_finite` by enumeration is only *coherent* AFTER
the witness-free axioms are replaced by constructive rules where possible. But note the
hard truth from S3′: **for the genuine Löb fixpoints there is no finite proof term to inject**
(the diagonal-lemma proof gives existence, not a term), so even "after constructive Löb"
`Provable` does not collapse to `Provable_finite` *at the fixpoints* — it collapses only on
the finite fragment.

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
   └──► Phase 4  constructive bounded Löb ───────► KILLS `PBLT` (as EXISTENCE thm only)
            │    mechanize critch22 Lemma 3.6: from S ⊢ □_{f(k)}φ(k) → φ(k), prove
            │    `∃ proof, …` for φ(k). ⚠️ CORRECTED: Critch's proof is the DIAGONAL LEMMA —
            │    it establishes a proof EXISTS, it does NOT build/exhibit a derivation term.
            │    So this removes the AXIOM (good) but the fixpoint still has NO extractable
            │    finite proof term (Computable.lean's "no finite play witness" STANDS).
            │    S3′ machine-checks why a term-builder can't be substituted in. Does close
            │    the `sorry`'d Löb matchups as existence results.
            │
            ├──► Phase 2  Decidable (Provable_FINITE k φ) ─► eval computable OFF fixpoints
            │        │    Enumerate proof terms of size ≤ k — terminates over a finite set.
            │        │    Decides `Provable_finite`, which = `Provable` ONLY off the Löb
            │        │    fixpoints. DecMeasure refutes the structural-recursion route;
            │        │    enumeration sidesteps it. Verified Fintype/enumerator over the
            │        │    size-indexed inductive + checker completeness (moderate engineering).
            │        │
            │        ┌──────────────────────────────────────────────────────────────┐
            │        │ ✗ STRUCK: "Phase 4 ⇒ every member has a witness ⇒ Provable    │
            │        │   decidable ⇒ eval computable AT THE FIXPOINTS." FALSE. Phase 4│
            │        │   gives existence, not a witness; the fixpoint members of      │
            │        │   `Provable` are NOT in `Provable_finite`, so enumeration does │
            │        │   not decide them. eval stays noncomputable at the fixpoints.  │
            │        └──────────────────────────────────────────────────────────────┘
            │
            └──► Phase 3  search_f constructor ─► KILLS `atom_complete_false_guard`
                     for the FINITE fragment: once `Provable_finite k φ` is decidable its
                     negation is too, so the Π₁ false-guard residue becomes a positive
                     constructor (`¬ Provable_finite k guard → … → PlaysProof … (.search …)`).
                     Easy GIVEN Phase 2. (Atom-layer, no fixpoint self-reference — safe.)
```

### Difficulty / axiom scorecard

| Axiom | Removed by | Difficulty | Helps eval-computability? |
|---|---|---|---|
| `box_provable` | Phase 1 (boxIntro) | moderate | no (axiom-shrink only) |
| `PBLT` | Phase 4 (Löb, as **existence** thm) | **hard / research** | **no** — existence ≠ witness |
| `atom_complete_false_guard` | Phase 3 (search_f, finite fragment) | easy *given Phase 2* | yes (finite fragment) |
| *(decidability of `Provable_finite`)* | Phase 2 (enumerate proof terms) | moderate-hard | yes, **off fixpoints only** |

End state (corrected): `Axioms.lean` shrinks (`box_provable`, `atom_complete_false_guard`
removed; `PBLT` demoted to an existence *theorem*) — possibly to just Lean's
`propext`/`Classical.choice`/`Quot.sound` if the `PBLT` existence theorem itself uses no new
axioms. `eval` becomes computable **on the finite fragment** and concrete fixed-`(k,fuel)`
**non-fixpoint** outcomes go `by decide`; ∀k-family theorems lean on a *proved* (existence)
Löb. **But `eval` stays noncomputable at the genuine Löb fixpoints**, and those concrete
outcomes are NOT `by decide` — they go through the existence theorem, exactly as today. The
project's noncomputability is **not** fully discharged: the fixpoint residue is the
proof-vs-witness gap (§2a ⚠️), which is permanent, not axiom-relative. Still not a Gödel wall
(finite fragment decidable) — but not liftable either.

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

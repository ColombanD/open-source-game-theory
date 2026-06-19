# Computable `eval`: the boundary

_Paper-section source material. The central evaluator `eval` is `noncomputable`; a
review flagged this. This document is the settled answer, structured the way the paper
section should run: the claim, why the limit is **fundamental to the theory** (not our
implementation), the artifact that exhibits the boundary, and what is safe to quote._

_Status: build green; no `sorry`; 4 axioms. All claims below are backed by checked Lean._

---

## 1. The claim

`eval` (and hence `play`/`outcome`) **cannot be made totally computable** while
satisfying its specification `proofSearch_spec`. This is a limit of the underlying
modal-fixpoint theory, not an artifact of how we coded it. What *is* achievable — and
what we ship — is a **sound, total, computable _partial_ evaluator** that agrees with
`eval` wherever it commits and otherwise abstains; the points where it abstains are
exactly the Löb fixpoints, and they are intrinsic.

The evaluator's only non-constructive ingredient is its `.search`-guard oracle:

```
eval … (.search k φ p q) … = if proofSearch k (φ.subst me opp) then run p else run q
proofSearch k φ := decide (Provable k φ)        -- classical, hence noncomputable
```

So "make `eval` computable" = "compute `proofSearch` = decide bounded `Provable`."

## 2. Why the limit is fundamental (the proof, in two parts)

The impossibility has a structural half and a semantic half. Either alone is
suggestive; together they are decisive.

### 2a. Structural obstruction — no naive well-founded measure (machine-checked)

`ComputableEval/DecMeasure.lean`. Deciding `Provable k φ` must recurse through the
`search_t` guard `Provable kg (ψ.subst me opp)`, where the guard budget `kg` is a
*source literal* (bounded by `2^k`, but **not** `< k`) and `ψ` is substituted with the
players `me`/`opp`. The natural termination measure — lexicographic
`(k, search-nesting-depth)`, justified by "`.bot` is a scope barrier so depth can't
grow under `subst`" — is **false**, by `decide`:

```
meP := .search 0 (.eq .self .self) .self .self        -- searchDepth = 1
(guard of meP).subst meP meP   has searchDepth = 2     -- self-substitution RAISES depth
```

Substituting a `.search`-bot into its own guard *increases* search-depth. Neither `kg`
nor the depth rank decreases on the guard recursion, so no naive structural recursion
bottoms out. This is the Löb self-reference made concrete: a guard can interrogate the
opponent (or itself) at a shape no smaller than the current one.

### 2b. Semantic obstruction — the spec forces `true` on witness-free outcomes

A terminating decision could only escape 2a by capping the guard recursion with an
external fuel parameter and then *proving it agrees with `Provable` at sufficient fuel*.
That agreement **cannot hold.** The library's cooperative fixpoints — canonically
`outcome_PrudentBot_vs_DupocBot = (C,C)` — are established not by unrolling a proof but
through the bounded-Σ₁ reflection axioms (`PBLT`, `atom_box_provable_impl`), and they
are reflected into the evaluator through `proofSearch_spec.2` (`Provable → proofSearch =
true`). These outcomes have **no finite proof-search witness** (Löb's theorem). Any
total function satisfying the existing `proofSearch_spec` would therefore have to return
`true` on them with no terminating search that finds why — impossible.

**Conclusion.** Total computability is precluded, full stop. `eval` must stay classical;
a computable evaluator must be a *separate, partial* object.

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
`outcome_PrudentBot_vs_DupocBot`, established via the reflection axioms — not a
computation. This is where bounded computation ends and modal reflection begins.

## 4. What this answers, and what to quote

- It answers the review point **honestly**: noncomputability is not sloppiness; it is
  forced (§2), and we both prove the impossibility and exhibit its precise locus (§3).
- It also addresses the related "too many axioms" point: during this work `c_guard_mono`
  was demoted from axiom to **theorem**. The remaining 4 axioms (`PBLT`, `box_provable`,
  `atom_box_provable_impl`, `atom_complete_false_guard`) are the modal-reflection
  primitives, orthogonal to computability.

Suggested framing for the paper:

> The evaluator's `.search` guard is a bounded-provability oracle. Deciding it totally
> is impossible: the guard recursion admits no well-founded structural measure (a
> self-substituted `.search` bot raises its own search-depth, machine-checked), and the
> library's Löb-fixpoint outcomes are reflected through the oracle's specification yet
> possess no finite proof-search witness. We therefore retain a classical `eval` and
> supply a separate, sound, computable *partial* evaluator `evalC`, proven equal to
> `eval` wherever it commits and returning `none` exactly at the fixpoints — locating
> the boundary between bounded computation and modal reflection.

**Quote-safe facts:** build green, 0 `sorry`, 4 axioms; `outcomeC_sound` (and its `eval`
/ `play` siblings) is fully proved; the `DecMeasure` counterexample is `decide`-checked;
the `none` at `PrudentBot × DupocBot` is reproducible via `#eval`.

**Do NOT claim:** that `evalC` is total, that it decides the fixpoints, or that
`DecMeasure` alone proves impossibility (it is the structural half; §2b is required).

---

## Provenance (not for the paper)

This file supersedes a chronological investigation log. Two total-computability routes
were tried and abandoned: a separate-search-gas `derivable` checker (non-monotone:
conflated "not found yet" with "unprovable"), and a `Decidable (Provable k φ)` instance
by a lexicographic well-founded measure (refuted by `DecMeasure.lean`, §2a). The shipped
result is route (D): keep classical `eval`, add the sound partial `evalC`. The artifacts
live in `engine/PrisonersDilemma/ComputableEval/` (`Computable.lean`, `Demo.lean`,
`DecMeasure.lean`); `c_guard_mono` is now a theorem in `Axioms.lean`.

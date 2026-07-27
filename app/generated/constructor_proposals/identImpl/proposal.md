# Constructor proposal: `identImpl`

*Filed by the proof agent on 2026-07-27. Status: **awaiting human review**.*

## The proposed `Pf` constructor

```lean
/-- **Propositional identity** (`⊢ φ → φ`): the reflexive implication is a theorem for any
        formula `φ`. Transcript cost pays the conclusion's own size (a leaf rule, like `eqRefl`).
        Sound: `interp (.impl φ φ) = (φ.interp → φ.interp)`, discharged by `fun h => h`. Faithful:
        a PA-like `S` proves `φ → φ` for every `φ` (propositional identity / reflexivity of `→`),
        a finite syntactic axiom-schema instance — no semantic completeness required. -/
    | identImpl (φ : Formula) :
        (Formula.impl φ φ).size ≤ k →
        Pf k (.impl φ φ)
```

## Soundness certificate — COMPILED against the current engine

`soundness_certificate.lean` (in this directory) proves the rule's interp-level content
as a theorem over the UNCHANGED engine. This machine-checks that the rule is TRUE; it
does not (and cannot) check faithfulness.

## Faithfulness rationale (agent-authored — REVIEW THIS)

A PA-like proof system `S` (critch22 Appendix B) proves `φ → φ` for every formula `φ`: this is the reflexivity of implication, a single instance of the propositional-identity axiom schema `A → A` (equivalently derivable from the Hilbert axioms K = `A → (B → A)` and S = `(A → (B → C)) → ((A → B) → (A → C))` in three steps). The syntactic activity transcribed is finite and bounded by the size of `φ`: writing down the fixed three-line schema instance with `φ` substituted. It is NOT semantic completeness or general reflection: the rule asserts nothing about the truth of `φ`, only the tautological structure of `φ → φ`; its soundness certificate `identImpl_sound` discharges the interp content with the identity function `fun h => h`, using no hypothesis about `φ`. The deliberate absence of a full implication-introduction (deduction theorem) in `Pf` — which would over-power `S` — is preserved: `identImpl` introduces ONLY the reflexive implication `φ → φ`, the one instance of implication-introduction that requires no discharged hypothesis and no consequent proof. This is strictly weaker than the deduction theorem (it cannot introduce `φ → ψ` for `ψ ≠ φ`), so it does not endanger the faithfulness/bound arguments that motivated omitting `→`-introduction.

## What this unblocks

llm_outcome_CIMCIC_vs_CIMCIC : ∃ k₂, ∀ k, k₂ < k → ∃ fuel, outcome fuel (CIMCIC k) (CIMCIC k) = some (.C, .C). CIMCIC's guard against a copy of itself substitutes to `A → A` where `A = .plays (CIMCIC k) (CIMCIC k) .C` — a genuine tautology (its `interp` is trivially true). With `identImpl` the guard `A → A` is provable at budget `k` (its size is O(log k) ≤ k for large k), so `proofSearch k (A → A) = true`, CIMCIC's `.search` fires the `.const .C` then-branch, and both copies cooperate: (C, C). I verified the ENTIRE downstream outcome proof compiles against the current engine when `identImpl` is assumed as a hypothesis (`∀ k φ, (Formula.impl φ φ).size ≤ k → Pf k (.impl φ φ)`): identImpl → Pf k (A→A) → proofSearch true → play C on both legs → outcome (C,C) via outcome_of_plays. Why no existing route: `A → A` is NOT derivable in the current `Pf` — every implication-introduction rule (`weakenImpl` needs a proof of the consequent `A`; `implTrans`/`impS2` need auxiliary implications; source-transparency/modal rules produce box- or plays-shaped implications, never a bare `φ → φ`), and proving `A` itself requires (via searchBranch `□_k(A→A) → A` + mp + boxIntro) a proof of `A → A` — the Löb loop our S cannot close without the identity axiom. Why not a defection theorem instead: the guard's `interp` is genuinely TRUE, so there is no interp-refutation; and structural unprovability is not tractable — the `mp` rule with an arbitrary antecedent breaks naive forbidden-set closure, and budget strong-induction fails because the `search_t` back-edge carries a fresh non-decreasing budget `k` (the guard proof `Pf k (A→A)` is not a transcript-smaller sub-derivation). Per the project's stated policy, a TRUE tautology guard is never bistable: since a faithful PA-like S proves `φ → φ`, the sound-and-faithful rule `identImpl` is the required exit, forcing the (C,C) fixed point.

## Integration checklist (human-initiated; see PF_ONLY_ROADMAP.md Phase 4 for scope)

- [ ] Faithfulness reviewed: is this a genuine capability of a PA-like `S`?
- [ ] Cost model reviewed: does the side-condition charge the transcript honestly?
- [ ] Constructor added to `ProofSystem.lean` (+ `sound_upto` arm, `Pf_mono` arm,
      `Pf.induct` hypothesis + wiring, `PlaysProof.induct` untouched)
- [ ] Engine target green — the floor/exclusion censuses are the canaries
- [ ] Metatheory: `PfG` mirror rule (+ gate decision), decider disjunct + completeness,
      T49 substrate node; both targets green
- [ ] Golden outcome inventory re-diffed

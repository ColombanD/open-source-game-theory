# Constructor proposal: `searchElseChain`

*Filed 2026-08-03 (proof-agent flow driven interactively). Status: **INTEGRATED** (2026-08-04) —
landed as `Pf.searchElseChain` with elseL guards restricted to plays-atoms stored structurally
(see meta.json integration_note). Both lake targets green; the first unblocked outcome
`llm_outcome_OptimBot_vs_DefectBot` = (D, D) at stagger `kSelf = 65536·kOpp` is proven.*

## The proposed `Pf` constructor

A mixed-polarity search-telescope reading rule — the `search_f` twin of `searchChain`,
completing Family A over ELSE-slot descent. New supporting definitions (additive,
alongside `searchPlug`/`ctxPlug` in `ProofSystem.lean`):

```lean
inductive SearchLayer2 where
  | thenL (g : Nat) (ψ : Formula) (e : Prog)   -- descend THEN; else branch e recorded
  | elseL (g : Nat) (ψ : Formula) (p : Prog)   -- descend ELSE; then branch p recorded

def plug2 : List SearchLayer2 → Prog → Prog
  | [], x => x
  | .thenL g ψ e :: L, x => .search g ψ (plug2 L x) e
  | .elseL g ψ p :: L, x => .search g ψ p (plug2 L x)

def guard2 (me opponent : Prog) : SearchLayer2 → Formula
  | .thenL g ψ _ => .box g (ψ.subst me opponent)   -- the guard search SUCCEEDS
  | .elseL _ ψ _ => .neg (ψ.subst me opponent)     -- the guard is REFUTED (Σ₁)

def layerCost : SearchLayer2 → Nat
  | .thenL g _ _ => c_guard g        -- cite of the fired guard's proof (as search_t)
  | .elseL g _ _ => g + c_node       -- the FULL failed budget — the search_f floor
```

The rule (premise-free source-reading leaf, like `searchChain`/`ctxChain`):

```lean
/-- S reads a mixed-polarity `.search` telescope: then-layers contribute `.box` guard
    antecedents (as `searchChain`), else-layers contribute `.neg` REFUTATION
    antecedents (the Σ₁ premise shape `search_f` consumes). Each else-layer's
    transcript pays its full failed budget — the `search_f` floor, forced by
    provable-soundness exactly as for `search_f`. -/
| searchElseChain (hd : SearchLayer2) (L : List SearchLayer2) (a : Action)
    (me opponent : Prog)
    (hme : me = plug2 (hd :: L) (.const a)) :
    layersCost (hd :: L) +
      (Formula.impl (guard2 me opponent hd)
        (implChain (guards2 me opponent L) (.plays me opponent a))).size ≤ k →
    Pf k (.impl (guard2 me opponent hd)
      (implChain (guards2 me opponent L) (.plays me opponent a)))
```

## Soundness certificate — COMPILED against the current engine

`soundness_certificate.lean` proves the rule's interp-level content as a theorem over
the UNCHANGED engine: `plug2_eval` (the mixed-polarity eval induction — the else
frontier twin of `searchPlug_eval`/`ctxPlug_eval` in `Base/ValuationSoundness`) and
`searchElseChain_sound`. The else-layer arm is the same consistency argument that
makes `search_f` sound: the refutation's truth plus `proofSearch_sound` forces the
guard search to fail, so `eval` takes the else branch.

**The floor is forced.** The `layerCost` of an else-layer must pay the full failed
budget `g`: in `sound_upto`'s budget-strong-induction, the arm for this rule must
refute a hypothetical guard proof `Pf g guard` that is NOT a sub-derivation — the
floor puts `g` strictly below the rule's own transcript so the outer IH supplies its
refutation. This is verbatim the argument in `search_f`'s docstring; without the
floor, provable-soundness breaks (and the T32-style budget dynamics would be at
risk). The cost model above preserves it.

## Faithfulness rationale (REVIEW THIS)

The rule claims exactly the capability `search_f` already grants `S` at the
`PlaysProof` level, lifted to the Family-A implication layer: *a PA-like S can prove
"my bounded search for ψ fails" by REPLAYING the failed enumeration — checking every
≤ g-length candidate — at a transcript cost of g characters* (critch22's literal
transcript model; `search_f`'s docstring calls paying `g` "generous, not inflated").
Note the antecedent is the Σ₁ refutation `.neg ψ'`, NOT an unprovability claim: the
rule never asks S to derive "search fails" from `¬ψ` alone (that would be internal
soundness-reflection, which S must not have — Gödel); the refutation is carried as an
undischargeable-except-by-`atomNeg` antecedent, and the failed-search replay is what
the transcript pays for. Family A currently reads: then-slot telescopes
(`searchChain`), ite probes of both polarities (`ctxChain`), and single failed
searches at the atom level (`search_f`). The else-slot of `.search` under a
hypothesis is the ONE remaining descent — this rule is the polarity completion of the
2026-07-28 family-completion program, not a new kind of power.

## What this unblocks

`llm_outcome_OptimBot_vs_DefectBot` at STAGGERED budgets — the flip that
`outcome_status.toml` records as expected ("Staggered kSelf >> kOpp expected to flip
to a PROVABLE (D,D); drop this entry when that theorem lands"). OptimBot's defection
against DefectBot lives at the end of an else-else-then-then path (two refuted
"DefectBot cooperates" rungs, the fired "DefectBot defects" rung, the rung-3
self-search): no current rule can internalize a play behind a FAILED search under the
box hypothesis, so the Löb premise `□_{kSelf} φD → φD` is underivable — see below.
With the rule: `unblocking_demo.lean` (COMPILED, rule as hypothesis in its exact
constructor shape, cost condition included) derives that premise at
`2·kOpp + O(log kOpp + log kSelf)` — two `search_f` floors plus logarithmic replay
overhead — via two `atomNeg` discharges and one `boxIntro`/`boxMono` discharge. At
`kSelf ≳ 8192·(2·kOpp + …)` the premise fits `bloeb_engine`'s budget schema (the
`optim_D_provable_at_k` pattern in `Theorems/OptimBot/vs_CooperateBot.lean`), rung 3
fires, and the outcome is `(D, D)`. The same skeleton then covers **OptimBot vs
TitForTatBot** and **OptimBot vs OBot** at staggered budgets (their actual D-plays
have cheap replay certificates via the already-provable exploit fact "OptimBot
defects vs `.bot CooperateBot`", so the refutations of "opponent cooperates" are
affordable) — three cells from one rule.

**Why no existing route** (why this is Tier-2, not a derivable Tier-1 lemma): the
impl-producers that can tail at a plays-atom of a non-const-branched searcher are
`searchChain`/`ctxChain` only, and both descend THEN slots — for OptimBot's D-play
their only decomposition carries the antecedent `□_{kOpp}("DefectBot plays C")`,
whose content is semantically FALSE, hence the box is unprovable (soundness) and
undischargeable — the chain can never yield the play. `weakenImpl` needs the
consequent outright, whose atom certificate needs `search_t` on the rung-3 self-guard
— an infinite regress at the `PlaysProof` level (each certificate embeds a real
`Pf kSelf φD`). `searchThenSearch_t` requires const-const inner branches (OptimBot's
rungs continue into non-const else programs). Deriving the else-crossing from
`.neg ψ'` inside `Pf` would require internalized soundness of the guard layer, which
S rightly lacks. The capability must be primitive, exactly as `search_f` is.

**What this does NOT unblock** (honest scope): the UNIFORM-budget outcomes
(`OptimBot k k` vs DefectBot/TFT/OBot/DBot/EBot/MirrorBot, semantically `(C, ·)` —
OptimBot falls through to its fallback C) need the NEGATIVE census
`¬ Pf k (OptimBot's own D-play)`, which hits the recorded implTrans/modal-tier wall:
the `searchChain` conclusion tailing at the D-atom is provable, so any forbidden
class must contain the boxed self-guard antecedent — a box-membered `TailToS` class,
which breaks the plays-only vacuity of every modal arm of the floor kernel. That is a
separate (kernel-side, derivable-machinery) project; this rule if anything ADDS one
more readable decomposition those censuses must price (see blast radius).

## Integration checklist (human-initiated; PF_ONLY_ROADMAP.md Phase 4 scope)

- [ ] Faithfulness reviewed: is the else-replay a genuine capability of a PA-like S?
- [ ] Cost model reviewed: floor per else-layer (`g + c_node`), `c_guard` cite per
      then-layer, conclusion size — does this charge the transcript honestly?
- [ ] `SearchLayer2`/`plug2`/`guard2`/`guards2`/`layerCost`/`layersCost` added next to
      `searchPlug`; constructor added (+ `sound_upto` arm via a ported `plug2_eval`,
      `Pf_mono` arm, `Pf.induct` hypothesis + wiring)
- [ ] Engine target green — the floor/exclusion censuses are the canaries: every
      `no_provable_tailToS_floor`/`no_provable_tailTo_floor` site gains a new
      obligation (kill/close the mixed-telescope conclusion; for existing zoo censuses
      the else-plug decomposition of the target player should be refutable
      action-refined, as today's `hplug`/`hctx` arms are)
- [ ] Metatheory: `PfG` mirror rule + gate decision (the else-layers cite guards the
      same way `search_f` does — the modest/instance gates need a stored-guard
      decision), decider disjunct + completeness, T49 substrate node; both targets
      green
- [ ] Golden outcome inventory re-diffed
- [ ] On acceptance: write `llm_outcome_OptimBot_vs_DefectBot` (staggered), then TFT
      and OBot; drop the `OptimBot/DefectBot` entry from `outcome_status.toml`

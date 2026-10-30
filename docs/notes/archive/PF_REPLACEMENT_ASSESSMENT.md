# Assessment — replacing `Derivation`/`Provable` with the unified `Pf`

> **2026-07-14 (later): DECISION — replacement is GO despite the price tag below.** The
> analysis here stands (it is the cost model the plan is built on); the migration plan is
> `PF_ONLY_ROADMAP.md`, which turns each finding into a phase or mitigation.

**Date**: 2026-07-14. **Status quo**: `Pf` is SHIPPED as a coexistence layer
(`PrisonersDilemma/Pf.lean`, root-imported): one `Prop`-valued budget-indexed proof-term type
(22 constructors vs the engine's 25), the EXACT transfer theorem `pf_iff_provable : Pf k φ ↔
Provable k φ` (`[propext]` only), `Pf_sound`, and the Löb/PBLT engines ported verbatim.
Validated on real bots (`Research/Spikes/unified_pf/PfEngineSpike.lean`): the CIMCIC exclusion
(one flat named induction) and DupocBot self-cooperation (critch22 Thm 3.7, end-to-end in `Pf`).

**The question assessed here**: what would it cost/buy to go further — retire
`Derivation`/`Provable` and make `Pf` THE proof system (the oracle
`proofSearch := decide (Pf k φ)`, `PlaysProof.search_t` consuming `Pf`)?

---

## 0. The one fact that changes the calculus: replacement de-unifies the induction

`Pf`'s headline ergonomic win — the NAMED `induction … with`, one flat induction for
exclusion proofs — is a property of the **coexistence design**, not of `Pf` itself. It holds
because `Pf` is a STANDALONE inductive: its `AtomProvable` premises are non-recursive, and
the execution layer's back-edge (`PlaysProof.search_t : Provable k guard → …`) still points
at `Provable`.

Under full replacement that back-edge must point at `Pf`, so `Pf` **enters the mutual block**
`{PlaysProofPf, AtomProvablePf, Pf}` — and Lean's `induction` tactic does not handle mutual
inductives. Every recursive induction over `Pf` reverts to the raw positional recursor
(32 minor premises: 9 + 1 + 22), exactly the style the unification was supposed to kill.

*Mitigation (one-time, bounded)*: hand-derive a named-hypothesis eliminator
(`Pf.induct`, `@[elab_as_elim]`, built once from the mutual `Pf.rec` with the
PlaysProof/AtomProvable motives pre-set to `True`-style throwaways where legal) so bot-facing
inductions keep named arms via `induction h using Pf.induct with …`. This works — but note the
engine never did it for `Provable`, and it is the same trick that would ALSO fix the current
system's ergonomics without any replacement. The honest conclusion: **the named-induction
argument favors coexistence, not replacement.**

> **Both halves MACHINE-CHECKED** (2026-07-14,
> `Research/Spikes/unified_pf/PfMutualInductSpike.lean`, full scale — the real 9+1+22
> mutual block over the real `Formula`/`Prog` with the `search_t` back-edge):
> (1) `fail_if_success induction h` confirms the tactic rejects the mutualized `PfM`;
> (2) `PfM.induct` (one theorem, one 32-arm recursor application; the motive must take the
> proof term — a proof-irrelevant motive breaks `induction using`'s target computation)
> restores fully named arms, demonstrated by `no_pfM_endsIn_falseEq` (22 named one-liner
> arms; `[propext]` only). The spike is the day-one artifact a replacement would ship.

What replacement DOES keep from the unification: no second reasoning type (the
`struct`→`Derivation` nested-induction hop is gone for good), one `mp`, one `implTrans`,
no glue, and one grammar for the metatheory's tree substrate.

---

## 1. Effect on the bot outcome proofs (engine proper: ~7.1k lines, Base/ + Theorems/)

The outcome STATEMENTS (`outcome_X_vs_Y = some (a,b)`, the `∃k₂` families) never mention
`Provable` — zero changes. The proof internals fall into four buckets:

| bucket | today | under replacement | verdict |
|---|---|---|---|
| **Transparency legs / guard provability** (19 `Provable.struct ⟨Derivation.…, size⟩` sites: `*_loeb_premise`, weakenImpl guards, eqNeg refutations, …) | build a `Type`-level tree, compute its tree size, glue | bare `Pf` constructors; multi-step trees become flat chains with per-step budgets (demonstrated: `dupoc_mirror_loeb_premise_pf`, same totals) | **shorter & flatter**; budget bookkeeping slightly more granular (one `≤` per step vs one tree-size `omega`) — a wash to mild win |
| **Löb/PBLT chains** (`mutual_loeb`, `bloeb_engine`, `pblt_engine*`, and every consumer) | `Provable`-level already | pure rename (demonstrated: `bloeb_engine_pf` is byte-shape-identical) | **neutral** |
| **Exclusion proofs** (CIMCIC/DIMCID forbidden-motive; `Base/Exclusion` census: `tail_plays_readable`, `no_provable_probeFirst_tail`, `no_provable_searcherPlay_tail` — the proofs behind all seven floor outcomes) | 5 raw mutual-recursor applications + nested `Derivation` inductions | one type fewer (no nested hop; 32 arms once instead of 26 + 9 nested) but STILL mutual ⇒ positional unless `Pf.induct` is built (§0). The census proofs over `PlaysProof` stay mutual-recursor-style regardless — they are about the execution layer, which no unification touches | **mild win with `Pf.induct`, mild regression without** |
| **`play`/`eval`/`outcome` lemmas** | — | `proofSearch` re-pointed at `Pf`; `proofSearch_spec`/`sound_upto` re-proved over the new mutual block (mechanical restructuring of `Base/Soundness`, the `Derivation` arms folding into the main induction) | **neutral after a real one-time port** |

Net for bots: a **full re-port of ~7k lines for a modest readability gain** — and the gain is
already MOSTLY available in coexistence, where new proofs (and LLM-pipeline generations) can
target `Pf` today and ship through the iff. The pipeline angle is worth stressing: a single
flat constructor set with named induction is a strictly friendlier target language for the
proof-writing agent than "which of two layers am I on?" — and coexistence already delivers it.

---

## 2. Effect on the Decidability metatheory and the open conjecture

The chain (~16k lines; 9 of 14 modules speak the gated mirror triple, 90 references to
`Derivation`) is married to the current grammar at three depths:

**(a) The gated mirror (`T42`): `PlaysProofG`/`AtomProvableG`/`ProvableG`.** A verbatim copy
of the engine triple with gates `G` on the six conclusion-absent premise formulas
(`implTrans`'s cut, `app`'s antecedent, `axK`'s boxed impl, `diagF`/`diagB`'s Löb premise,
`impS2`'s cut). Under replacement this becomes a mirrored `PfG` — one type instead of three,
but every gated rule re-stated and every soundness/completeness bridge re-proved.

**A real design decision hides here.** Today `ProvableG.struct` wraps the **ungated**
`Derivation`: `Derivation` trees are self-bounding (a `d.size ≤ k` bound pays every internal
cut structurally), so their `modusPonens`/`hypSyll` cuts pass NO gate. In unified `PfG`, the
merged `mp`/`implTrans` carry the gate — so ex-`Derivation` cuts become **gated where they
were free**. Consequences:
  * `PfG (instGate P N)`/`(litGate N)` is not literally the image of today's stratum; the
    stratification theorem `Provable ↔ ∃N, ProvableB N`, the certified zoo (T54: every zoo
    tree re-certified with its ex-`Derivation` cuts now discharging gate obligations — likely
    fine, since zoo cut formulas are pool-program plays-atoms, i.e. exactly instance-gate
    shaped, but "likely fine" = re-proved), and the falsification theorem (T51) all need
    re-establishing against the new stratum.
  * Alternatively one could gate `mp`/`implTrans` only conditionally (free below the budget's
    structural bound) — but that reintroduces a two-tier rule set inside the single type,
    i.e. the complexity the merge was meant to remove.

**(b) The enumerator and the substrate.** `decFull` (T31, ~2.1k lines) enumerates the
triple + `Derivation` (with its `Type`-level size recursion) — a unified enumerator over one
grammar is genuinely SIMPLER, but it is a rewrite, and `Provable_iff_decFull` with it. The
T49 tree substrate (~6k lines: extraction machine, normalization, excisor) models proof
trees as a datatype; today that grammar spans `Derivation` nodes, `Provable` nodes, and the
`struct` boundary between them. A unified grammar removes the boundary-crossing cases —
probably the single largest genuine simplification replacement buys — but T49 is also the
single largest file to rewrite.

**(c) The open conjecture (universal closure:
`Provable k φ → ProvableG (instGate P N₀) k φ` for arbitrary minimal proofs).**
Two separate observations:

  * **Replacement does not advance it.** The hard content — the diag cite regress, composing
    excision with the cite/rawness transport certificates — is about the FIXPOINT rules and
    the gate, both of which survive unification unchanged. Rewriting the substrate mid-hunt
    would stall the conjecture for the duration of the port.
  * **Coexistence already helps it, today.** `pf_of_provable` + a `Pf`-induction is a NEW
    single-induction principle over full `Provable`: a closure proof can case on 22 flat
    constructors instead of `Provable.rec`-plus-nested-`Derivation`-lemma. The `struct` arm —
    which today forces every closure-style argument to prove a separate `Derivation` census —
    disappears into the `mp`/`implTrans`/leaf arms. The gate obligations per cut are the same
    mathematics, but the induction skeleton is cleaner. If/when the closure is attempted,
    attempt it through `Pf`.

---

## 3. Verdict

* **Coexistence (shipped) is the right resting point.** It delivers the readable proof
  language (flat legs, named exclusion inductions, one MP), costs nothing further, keeps the
  metatheory untouched, and even improves the induction toolkit available for the open
  conjecture. Point the LLM pipeline's proof agent at `Pf` (few-shots from the spike demos;
  ship via `provable_of_pf` or state theorems over `Provable` and convert at the top).
* **Full replacement: defer, and probably rethink its selling point.** Price: ~7k engine
  lines + ~16k metatheory lines re-proved, the gate-on-ex-`Derivation`-cuts design question
  (§2a), and — the under-appreciated cost — `Pf` becomes mutual, so the named-induction
  ergonomics REGRESS to positional recursors unless a custom eliminator is built (§0).
  Payoff: −3 constructors, no struct boundary in the T49 substrate, one enumerator.
  That trade only makes sense bundled with the post-universal-closure rebuild (when T49-scale
  surgery is happening anyway), and only WITH the `Pf.induct` eliminator built on day one.
* **If the itch is induction ergonomics** (the original complaint the sketch addressed):
  the cheapest global fix is not replacement at all — it is deriving named
  `@[elab_as_elim]` eliminators for the EXISTING mutual block, plus coexistence-`Pf` for
  everything new. Both are now available.

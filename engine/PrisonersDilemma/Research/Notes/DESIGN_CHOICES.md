# Design Choices

A running log of load-bearing design decisions in the engine: what was chosen, what
forced it, what was rejected, and how to route around it. Newest entries at the top of
each era. Companion notes: `DECIDABILITY_ROADMAP.md` (the T31…T54 arc),
`CUT_RELEVANCE.md` (the falsification/repair history).

---

## Story 2 in brief — from a sound oracle to a decidable one (T31…T54, 2026-07-03 → 07-09)

Story 1 ended with a sound engine whose evaluator is CLASSICAL: `eval`'s guard is
`decide (Provable k φ)` — correct, noncomputable. Story 2 is the campaign to turn that
oracle into an algorithm. Five phases; everything lives in `Decidability/`.

**A — Run it, with an asterisk (T31).** `decFull`: a computable enumerator with
`Provable k φ ↔ ∃ fuel, decFull fuel k φ = true` — keep a table of "provable so far",
each round try to fire every rule against the table, iterate. On top, `evalG`: the
computable evaluator; programs run directly, `.search` guards consult the oracle,
which answers `some true` (proof found), `some false` (refutation found), or `none`
(undetermined). A `none` can mask either polarity at fixed fuel; in the limit it masks
exactly the false-but-IRREFUTABLE guards (the anti-diagonal's own — the honest
Gödelian residue). The asterisk: semidecidable — yes-answers eventually, but no
STOPPING BOUND after which "not found" means "no".

**B — Buy a stopping bound (T42–T47).** Two infinities block a bound. (1) CUTS: six
rules (`app`, `implTrans`, …) use a stepping-stone formula absent from the conclusion
— infinitely many candidates. Fix: real proofs write their stepping-stones inside the
transcript, so `Provable` decomposes into GATED strata `ProvableG G` (cut positions
must pass gate `G`) with `Provable ↔ ∃N, ProvableB N` — nothing lost in principle.
(2) QUERIES: deciding one guard spawns new questions (substitution creates new
player pairs and instances). Fix: zoo bots are MODEST (sim/guard arguments are only
`.self`/`.opp`/frozen closed bots, checkable by `rfl`), and modest dynamics can never
invent new material — every reachable question lives in one computable finite list
`SL`. Then saturation over a finite space must stabilize within `|SL|` rounds
(pigeonhole): `Decidable (ProvableG (modestGate N) k φ)`. Remaining question
(CutRelevance): is the modest stratum the WHOLE truth about the zoo?

**C — Proofs as data (T48–T49).** To reason about ALL proofs of a fact: `ProvT`, the
`Type`-valued mirror (`Provable k φ ↔ Nonempty (ProvT k φ)`) — proof TREES you can
measure and walk; the census (T48: every implication a `Derivation` proves has a
catalogued antecedent; literals `< 2^budget`); and the rewriting machine (T49): a
cut-eliminator (β-reduce stepping-stones away) with a Tait-style normalization theorem
proving it always halts, packaged as the excisor + kernel-decidable certificate
families. Built expecting to PROVE CutRelevance by rewriting any proof into the
stratum.

**D — The falsification (T50 witness, T51 theorem).** Test the hardest fact: Dupoc's
self-cooperation (the Löb fixpoint), written as a concrete tree — it FAILS the modest
gate. And unfixably so: `cutRelevance_modestGate_false` — the fact is `Provable` but
`¬ProvableG (modestGate N)` at EVERY `N` and budget. Simply put: a Löb proof must at
some point hold the exact self-referential sentence ("Dupoc plays C vs Dupoc" — full
of concrete bot code) in the very positions the gate restricts to generic shapes, and
must apply `diag` to it; block that and every proof attempt is circular (the guard's
content IS the conclusion — citing it re-derives the goal at no budget descent;
infinite regress, closed case-by-case). The conjecture is FALSE, and informatively:
the decidable modest stratum excludes exactly the cooperation facts the zoo runs on.

**E — The repair (T50, T52–T54).** The autopsy is the spec: the gate wrongly demanded
genericity where the zoo needs INSTANCES — argument slots holding pool bots or closed
modest code, guards stored raw. That is the instance gate `instGate P N`. Surprises,
in order: the real Löb trees pass it RAW (no rewriting — Phase C's machine was needed
for the refutation and the certificates, not surgery); the TRANSPORT theorem replaces
inspection with a 4-item mechanical checklist (`certifyTransport`: gated cuts, capped
cites, raw atom frames, instance conclusion → the whole tree is in the stratum); the
decider was gate-parametric all along (T52: the gate enters at eight sites) and the
finite-space stabilization survives (T53: instance cuts' arguments re-enter `SL`) —
`decideProvableG_inst`, decidable with the same `|SL|` bound. T54 then certifies every
guard fact the zoo consults (kernel-evaluated checks, incl. Prudent×Dupoc at
`k = 2²⁹`). NET: the zoo's oracle is an algorithm with a computable stopping bound.
OPEN: the universal closure — arbitrary provable facts transport (excise + certify
composed for arbitrary trees) — on which certificate-free uniform computability rests.

**The algorithm, and why saturation.** All deciders are bottom-up Kleene saturation
(monotone table + step operator + pigeonhole), NOT goal-directed backward search.
Chosen for the smallest trusted correctness argument (monotonicity + pigeonhole +
step congruence — the proof burden dominated the choice), and because backward search
LOOPS on precisely the Löb fixpoints (the guard instance cites itself; T51's regress
is that loop) — bottom-up reaches fixpoints from below via `diag` instead of chasing
cycles. Also: the same operator, fuel-indexed, IS the semidecider `decFull`; and gate
parametrization is mechanical. Efficiency was a NON-goal: the combinatorics are
intrinsically exponential, and practical use rides the find/verify asymmetry — search
offline, check the four cheap transport certificates in the kernel (that is how the
`2²⁹` facts are settled without running the astronomic search). Known,
theorem-preserving optimizations if ever needed: semi-naive evaluation (the saturation
over `SL` is essentially ground Datalog), demand-driven restriction, hash-consing —
or an untrusted fast searcher emitting kernel-checked certificates, the architecture
the transport theorem was built for.

---

## The `search_f` floor: else-certificates cost `n + m + k + c_node` (2026-07-02)

**The decision.** A `PlaysProof` for a search bot's *else*-play (the branch taken when
the guard search fails) is only constructible by `PlaysProof.search_f`, whose premises
are (i) a Σ₁ **refutation** of the guard instance, `Provable m (.neg (φ.subst me opp))`,
and (ii) a certificate for the else branch (`n`); and whose **cost is
`n + m + k + c_node`** — the bare `k` summand is the *full failed search budget*,
charged unconditionally. We call that summand **the floor**.

**Why a refutation premise at all.** The predecessor rule (`atom_complete_false_guard`,
an axiom) granted else-certificates from mere *meta-falsity* of the guard, at small
cost. It was machine-checked **inconsistent** (`Research/Spikes/transcript/
T32Inconsistency.lean`). The refutation premise is the honest Σ₁ substitute: S may
certify an else-play only when it can *exhibit evidence* the guard fails (via
`Provable.atomNeg` — the actual play refutes the claimed play by eval determinism — or
`Derivation.eqNeg`).

**Why the floor — the anti-diagonal counterexample.** Suppose else-certificates could
cost ≤ k. Take the anti-diagonal bot

```
A := .search k (.plays .self .self D) (then: .const C) (else: .const D)
```

— "if I can prove I defect against myself, cooperate; else defect."

1. The guard cannot be provable: if `Provable k (A plays D vs A)`, soundness makes it
   true, but a provable guard makes `A` play **C** — contradicting the very play the
   guard asserts.
2. So the search fails and `A` really plays D — the else branch.
3. A cheap else-certificate would now place "`A` plays D vs `A`" inside `Provable k`.
   But that atom **is the guard**. The guard just became provable at k, so `A` plays C
   — and eval determinism yields machine-checked `False`.

So *any* consistent accounting must charge **> k** for an else-certificate: the
certificate asserts the very fact whose sub-k provability would flip the play it
certifies. Our `n + m + k + c_node` with `n, m ≥ 1` sits at `k + 3` — three characters
above the cliff, each one a real transcript component (branch replay, refutation, rule
node). There is no slack.

**Three independent forcings of the same summand:**

- **Consistency** — the anti-diagonal argument above.
- **Provable soundness** — `sound_upto` (Base/Soundness.lean) is a strong induction on
  the budget; the `search_f` case needs the inductive hypothesis *at budget k* to turn
  the refutation into genuine search failure (`¬Provable k (guard)`), which requires
  `k <` the conclusion's cost. The floor is exactly what makes the induction go through.
- **Decidability** — transcript-cumulative costs with the floor make every premise
  budget strictly smaller than the conclusion's, which is what makes bounded proof
  search genuinely finite (the T31…T54 arc).

**The Σ₁/Π₁ asymmetry (why `search_t` is cheap and `search_f` is not).** A *successful*
search has a witness — the found proof — and citing a witness costs `c_guard k =
numCost k = log₂ k + 1` (the numeral). A *failed* search has no witness: "no proof of
length ≤ k exists" is Π₁ over the search space. A short certificate of one's own failed
k-search would be a bounded proof of one's own consistency-at-k — the floor is bounded
Gödel II wearing a cost annotation.

**We undercharge, if anything.** Under Critch's literal reading (the verifier re-checks
the transcript), honestly verifying "the k-search failed" means re-running the
enumeration: exponential in k. We charge *linear* k — a receipt, not a re-run. The
accounting sits at the consistency-minimal point, exponentially below the
literal-verification price. "Too strong" is backwards.

**Rejected alternatives (do not retry):**

| Alternative | Fate |
|---|---|
| No premise, meta-truth suffices (the axiom) | Inconsistent, machine-checked (T32) |
| `¬Provable k g` as a premise (unprovability-premised `search_f`) | Non-monotone fixpoint — not even a proof system; the anti-diagonal is its paradox; kills r.e.-ness, hence `decFull`, hence decidability |
| Refutation premise, no floor (`n + m + c_node`) | Breaks `sound_upto`'s strong induction (needs IH at budget k below the conclusion cost) |
| Oracle receipts ("point at `decFull`'s run") | Reflection smuggled back in: a short Π₁ certificate about S itself — same Gödel II wall |

**How to route around it (bot level, not rule level):**

1. **Staggering** — a *different* bot's budget pays the floor:
   `PrudentBot (2k+64)` affords certificates about `DupocBot k`'s failures.
2. **Two-tier bots** — `PrudentBot2`: an internal budget hierarchy; the outer tier pays
   the inner tier's floor (the bounded rediscovery of MIRI PrudentBot's PA+1 prudence).
3. **Simulational guards** — `.sim` is run-priced, no floor. Probing by *running*
   dodges the floor entirely (DBot's whole side of DBot×DupocBot is certifiable for
   pennies).
4. **The freeze trick** — replace `.self` in the guard by a FROZEN weaker snapshot and
   raise the asker's budget: `JustBot2 K k` (guard target `.bot (DupocBot k)`, search
   budget `K ≥ k + log₂ k + 26`) — see the dedicated section below.

What the floor kills, unavoidably: *same-budget self-referential* cooperation — pairs
where the partner's play crosses the searching bot's **own** failed search at the
searcher's own budget (DupocBot×DBot, DupocBot×EBot, PrudentBot×EBot). The floor chases
the budget (the failed search and the asking guard are the same `.search k` of the same
bot, glued by `.self` substitution), so no stagger fixes them. Their honest outcomes
are defection on the searcher's side; formalizing those needs a `¬Provable k` cost
lower bound — nontrivial because the guard formula is TRUE (soundness gives nothing).

**The lower bound, delivered for ALL SIX floor pairs (2026-07-09).** `Base/Exclusion.lean`
proves the reusable **Derivation census** (`tail_plays_readable`: only the five
bridge-readable player shapes can appear as a plays-atom spine tail of a `Derivation`)
and the **generalized floor bound** `no_provable_probeFirst_tail` (+ the
`_botOpp` variant for a `.bot`-wrapped searcher): for any probe-first simulator
`.ite (.sim .opp (.bot z)) aT p q` — test action and BOTH branches fully general, since
the kill happens at the guard certificate that both `ite` polarities must carry —
against any budget-`k` searcher (`.search k g pT pE`, bare or `.bot`-wrapped) whose
guard instance vs the probe is false, no ≤ k certificate concludes the simulator's
play. Strong induction on the budget: `struct` dies by the census, `atom` dies inside
the `PlaysProof` replay (`search_t` by soundness of the false probe guard, `search_f`
by the literal floor summand), and the `app`/`weakenImpl`/`implTrans`/`diagF`/`impS2`
regress descends by transcript cumulativity. Every floor tombstone falls as an
instance (the floor fires at the FIRST probe, before the simulators' branches differ):
* `outcome_DupocBot_vs_DBot = (D, C)` at every budget (`Theorems/DupocBot.lean`);
* `outcome_DupocBot_vs_EBot = (D, C)` for every `k ≥ 2` (ibid.; the bound is the Σ₁
  price of the `.bot CooperateBot` probe certificate steering EBot's second guard);
* `outcome_PrudentBot_vs_EBot = (D, C)` past the Löb threshold
  (`Theorems/LlmGenerations/PrudentBot.lean`; EBot's third probe watches the
  PrudentBot↔`.bot MirrorBot` Löb cooperation, so EBot's C-play itself rides
  `prudent_botmirror_coop` — a negative-outcome theorem whose positive half is PBLT);
* `outcome_CupodBot_vs_OBot = (C, D)` for every `k ≥ 2` (`Theorems/CupodBot.lean`; the
  defection-DETECTOR gets exploited — OBot's real defection is uncertifiable within
  Cupod's own budget, so Cupod cooperates into the sucker payoff; target action D and
  a then-branch `ite`, exercising the lemma's full generality);
* `outcome_JustBot_vs_DBot = (D, C)` at every budget and
  `outcome_JustBot_vs_EBot = (D, C)` for `k ≥ 2`
  (`Theorems/LlmGenerations/JustBot.lean`; the `_botOpp` variant — JustBot's guard
  target is the FROZEN `.bot (DupocBot k)`, one extra `.bot` unwrap in the replay).

* `outcome_PrudentBot_vs_PrudentBot = (D, D)` at every budget
  (`Theorems/LlmGenerations/PrudentBot.lean`; the THIRD exclusion shape,
  `no_provable_searcherPlay_tail` — the target atom is the SEARCHER'S OWN else-play,
  no simulator detour: PrudentBot's self-prudence "I defect vs `.bot DefectBot`" is
  floor-blocked at its own budget, so single-tier prudence is self-defeating and
  same-`k` self-play is mutual defection; the cooperative fixed point exists only one
  tier up, `outcome_PrudentBot2_vs_PrudentBot2`).

The same-`k` retirements with STAGGERED/two-tier replacements (PrudentBot×DupocBot,
JustBot×PrudentBot, JustBot×CupodTrollBot) were already re-certified during the
repair; with the seven honest theorems above, NO retired outcome remains unreplaced.
Optional future work: the same-`k` DEFECTION outcomes for those three staggered pairs
(e.g. Prudent k × Dupoc k = (D, D)) need an ACTION-AWARE census — Dupoc/Cupod-style
both-const searchers ARE bridge-readable (`searchBranch`), but only their THEN-action
plays; refining `ReadableMe` to carry the action would close them. Genuinely open
matchups (JustBot×MirrorBot's bistable fixed point) are open for semantic reasons,
not missing lower bounds.

---

## Single-tier prudence is self-defeating — a structural theorem, not a syntax choice (2026-07-09)

**The question.** `outcome_PrudentBot_vs_PrudentBot = (D, D)` at every same-`k`. Is this
an artifact of PrudentBot's syntax (nesting order, then/else polarity) or of
`searchThenSearch_t`'s design — could either have been arranged differently to recover
same-budget cooperative self-play?

**No — and in the strongest sense: `(D, D)` is a fact about `eval`, not about the proof
rules.** At same-`k` the bot REALLY defects against itself; the outcome theorem reports
what the evaluator does. Any rule change that let `S` conclude "I play C vs me" while
`eval` plays D would certify a false play — exactly the unsoundness that killed
`atom_complete_false_guard`. Rule design is only ever to blame when a TRUE play is
uncertifiable; here the cooperation is genuinely absent at runtime.

**Where the classical Löb route dies.** Bounded Löb (`pblt_engine`) consumes
`□_k("I play C vs me") → ("I play C vs me")` as its HYPOTHESIS. For a plain search bot
(DupocBot) that implication is a one-leaf `searchBranch` read — free, so Dupoc
self-cooperates. For PrudentBot's stacked shape the only producer is
`searchThenSearch_t`, whose premise list PRE-PAYS the inner prudence guard:
`Provable m (inner instance)` with `m ≤ k₂`. In self-play the prudence instance is
"PrudentBot k plays D vs `.bot DefectBot`" — the else-play of its OWN outer `k`-search,
floored above `k` (`no_provable_prudence_self_tail`). So the chain dies at step zero:

```
prudence cert (≤ k) → searchThenSearch_t → □φ→φ → pblt_engine → guard fires
      ✗ floor            never assembled     no hyp    never runs     false
```

Löb is never handed its hypothesis; cooperation is then FALSE (the bot plays D), so
soundness settles the outer guard. (The Lean proof case-splits on the outer guard
instead of running this analysis — proving the guard false directly would circularly
need the play first; the true-branch is vacuous-but-handled via the floored prudence.)

**Syntax shuffles don't help — the floor follows the single budget:**

| Variant | Fate |
|---|---|
| Prudence outside, cooperation inside | Self-prudence now routes through the INNER cooperation search failing vs DefectBot — floor still `k`. Worse: `searchThenSearch_t` would have to pre-pay the inner guard = the cooperation fixpoint itself — circular; Löb shape destroyed. |
| Flipped polarity (negative prudence, cooperate on the inner ELSE) | Needs a `searchThenSearch_f` premised on a REFUTATION of the prudence guard; `atomNeg`'s refutation requires the certificate of the ACTUAL play — the same floored else-play. The floor blocks both polarities. |
| Simulational prudence (`.ite (.sim .opp (.bot DefectBot)) …` wrapping the search) | Runtime prudence becomes fuel-priced — but self-cooperation still needs Löb through the cooperation search, and the only bridge (`iteBranchSearch_t`) is guarded by the ATOM "me plays D vs botDefect", which S must discharge — floored, one step removed. |

The invariant: self-prudence is a fact about MY OWN play against DefectBot, and any
single-budget bot's play against DefectBot crosses a failed `k`-search somewhere (a
sound system can never prove "DefectBot cooperates", so whichever search asks, fails).
The certificate carries that search's floor — always `k`, because there is one dial.

**`searchThenSearch_t` is already at its generosity limit.** Its inner premise is
CITED, not charged: the size condition pays only `c_guard k₂ = log₂ k₂ + 1`,
non-cumulatively (charging it fully sinks the staggered Löb chains — see the dead-ends
list). The one unremovable condition is `m ≤ k₂`, and it is not an accounting choice
but the bot's own source: `eval` produces the then-play only if the inner guard is
provable AT `k₂`. Drop the bound and the rule asserts plays the evaluator doesn't make.

**The deep reason (bounded Gödel II, and the MIRI parallel).** Bounded self-prudence
IS bounded self-consistency: "I defect vs DefectBot" holds because my own search
FAILS, and certifying one's own failed `k`-search within `k` is the floor's Gödel II
wall. The unbounded literature hit the identical obstruction: MIRI's PrudentBot runs
its prudence check in **PA+1**, not PA. `PrudentBot2` (`kIn = 4k+100 > kOut = k`) is
the bounded transcription, and the mechanization upgrades the folklore to a
machine-checked DICHOTOMY: `no_provable_prudence_self_tail` proves the single-tier
wall, `prudence_P2` + the two-tier `searchThenSearch_t k (4k+100)` application prove
the escape, and the entire PA/PA+1 gap compresses to one inequality —
**floor cost ≤ inner budget** — false at `(k, k)`, true at `(k, 4k+100)`.

---

## The freeze trick: `JustBot2` — staggered self-reference via frozen snapshots (2026-07-09)

**The question.** The floor pairs' `(D, C)` outcomes (DupocBot×DBot etc.): could budget
tuning have rescued cooperation there too, as `PrudentBot2`'s two tiers rescued
self-play?

**Not by tuning the searcher itself.** `PrudentBot2`'s escape needed two DIFFERENT
search nodes with independent dials, arranged well-foundedly (inner consumes outer's
failure). DupocBot has ONE node, and its guard's `.self` makes the requested fact
("DBot plays C vs ME") about the very node doing the asking: DBot's probe makes THAT
node fail, so the floor is the asking node's own budget — one node, one dial, turning
it moves floor and budget together. `.self` in a guard closes the dependency loop at
the top tier; no assignment of numbers to a single parameter opens it.

**The escape: break `.self` with a frozen weaker snapshot.** Replace the guard's
`.self` by `.bot (DupocBot k)` and give the asking search a bigger budget `K` — the
requested fact now crosses the SNAPSHOT's floor `k`, not the asker's:

```
JustBot2 K k := .search K (.plays .opp (.bot (DupocBot k)) .C) (.const C) (.const D)
```

This is exactly JustBot's architecture — `JustBot k = JustBot2 k k` — and the
single-parameter tying is the sole reason `outcome_JustBot_vs_DBot = (D, C)`:

* `provable_DBot_C_vs_botDupoc` — the staggered certificate, constructed by hand:
  DBot's `ite` replay over the snapshot's `search_f` (floor `k`, `atomNeg` refutation)
  costs exactly **`k + log₂ k + 26`**;
* `outcome_JustBot2_vs_DBot = (C, C)` for `JustBot2 (2k+64) k`, at EVERY `k` — the
  FairBot×DBot handshake recovered at staggered internal budgets
  (`Theorems/LlmGenerations/JustBot.lean`).

The constructive companion to the floor impossibilities: the `(D, C)` outcomes are
theorems about budget-TIED bots, not about the matchups.

**The price — proxy ≠ self.** The semantics change from "cooperate iff you provably
cooperate WITH ME" to "…with my weaker past self". The snapshot is not the bot: an
opponent could in principle cooperate with `DupocBot k` yet defect against
`JustBot2 K k`, and JustBot2 would be suckered — a spoofing surface genuine `.self`
guards don't have. (DBot cannot exploit it — its probe is `.bot DefectBot`-directed,
blind to the distinction — which is why the handshake above is safe.)

**The design dichotomy (the general lesson).** Bounded agents purchase mutual
legibility in exactly two currencies:

1. **Löbian self-fulfillment** — same tier, `.self` guards, genuine "with me"
   semantics; works ONLY for self-fulfilling (cooperation-shaped) facts, never for
   failure facts (`outcome_PrudentBot_vs_PrudentBot = (D, D)`);
2. **Budget hierarchy over frozen proxies** — any facts (including failures), but the
   introspection must point strictly DOWN the budget order (frozen snapshots are how a
   bot refers to lower tiers of itself), and proxy ≠ self is a real semantic gap.

There is no third option at a single tier — that is the content of the floor theorems.
Recipe for future bots: put only self-fulfilling fixpoints at the top tier; route
every failure-fact a guard consumes through a strictly lower tier (internal two-tier
budgets à la `PrudentBot2`, or frozen snapshots à la `JustBot2`).

---

## Transcript-cumulative costs — Route B (2026-07-02)

Every `Derivation`/`Provable` cost is **cumulative**: a rule's conclusion cost contains
its premises' costs as summands (a transcript is the concatenation of its
sub-transcripts; no sharing, no compression). This is Critch's literal "`k` means
characters of proof transcript" model. The payoff: cut/premise formulas are
budget-bounded *for free* (a premise's transcript is part of the conclusion's), which
is what dissolved the mp-cut wall (`MN1_decidable.lean`, conclusion-cost model — dead
end) and made the logical fragment of `Provable` decidable relative to the atom layer.
Corollary used everywhere: `Derivation.concl_size_le` — a conclusion's size is at most
its derivation's size.

---

## `numCost` — single source of truth for the numeral price (2026-07-05)

`numCost k := Nat.log2 k + 1` (Program.lean) is the *one* definition of "what it costs
to write the numeral k". `Prog.size` (`.search`), `Formula.size` (`.box`/`.diag`) and
`c_guard` all consume it. Rationale: the three call sites had drifted-copy risk, and
every Löb-chain budget bound routes through this quantity. Refactor note: `omega`
treats `numCost` as opaque — simp sets that unfold `Formula.size`/`Prog.size`/`c_guard`
must also unfold `numCost`.

---

## `Base/` split + the `Metatheory` lake target (2026-07-09)

`BaseTheorems.lean` (1057 lines) split by role into `Base/Asymptotics` (log₂
arithmetic; absorbed `SizeLemmas.lean`), `Base/AtomCerts` (constructive atom
certificates), `Base/Soundness` (`sound_upto`, `Provable_sound`), `Base/Loeb`
(`bloeb_engine`, `pblt_engine`, mutual engines). `BaseTheorems.lean` remains as a
re-exporting umbrella and every name keeps its `PD.BaseTheorems` (resp. `PD`) full name
— importers unchanged. Simultaneously, the lakefile grew a second `lean_lib`:
`PrisonersDilemma` (engine + zoo; the root no longer imports `Decidability`) vs
`Metatheory` (rooted at `PrisonersDilemma.Decidability`). Both are default targets;
the engine never imports the metatheory.

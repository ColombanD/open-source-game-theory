# Design Choices

A running log of load-bearing design decisions in the engine: what was chosen, what
forced it, what was rejected, and how to route around it. Newest entries at the top of
each era. Companion notes: `DECIDABILITY_ROADMAP.md` (the T31…T54 arc),
`CUT_RELEVANCE.md` (the falsification/repair history).

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

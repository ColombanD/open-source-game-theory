# The Bot Reviewer — design, status, and the rewriter loop

**Status as of 2026-08-05:** Tiers A1, A2, and B are implemented and wired into
`run_bot_pipeline`. The rewriter loop (§7) and the E2 harness (§8) are designed
here but NOT built.

**Scope.** This document owns the faithfulness half of the NL→bot pipeline: given
a natural-language strategy description and a generated Lean bot, decide whether
the bot actually implements the strategy. It does not cover the bot writer itself
(`services/bot_service.py`) or the proof agent.

**Related:** `CLAUDE.md` Phase 3 milestone 4 carries the summary; the per-component
reasoning lives in the module docstrings of `services/bot_expectation.py`,
`services/bot_profile.py`, and `services/bot_judge.py`. This file is the design
rationale and the forward plan — read it before changing the architecture.

---

## 1. The hole this closes

The bot writer's only acceptance gate was **"it compiles"** (`llm/prompts.py`,
bot rules). `Prog` is permissive enough that essentially every well-typed term
compiles: `.const Action.C` compiles perfectly for the prompt *"defect against
bullies"*. Compilation therefore carries almost **zero signal** about whether the
bot means what the description says.

This is the one place in the whole system where correctness is not machine-checked.
`CLAUDE.md` names it: *"NL→Lean translation accuracy is the remaining weak link."*
The project's headline claim — **compilation == correctness** — is explicitly
qualified *modulo the NL→Lean bot translation*, and that modulo was unguarded.

Failure modes that actually bite. All of these compile, and all of them read
plausibly in review:

| Failure | Example |
|---|---|
| Probe target frozen vs substituted | `.bot SomeBot` where the description implies `.opp` (the JustBot `subst` bug) |
| `.self`/`.opp` swapped in a `.plays` atom | "you cooperate with me" vs "I cooperate with you" |
| Guard polarity inverted | then/else branches exchanged — see §5, this one got past a judge |
| Refutation vs assertion | `.neg (.plays … C)` vs `.plays … D` — equal semantics, different proof machinery (the whole point of WaryBot) |
| Wrong arity on a multi-budget bot | applying `OptimBot (kOpp kSelf)` to one argument yields `Nat → Prog`, never a `Prog` |

That last one was live in `outcome_prepass.py` until 2026-08-05 and silently
invalidated every OptimBot result. See §6.

## 2. Architecture — two tiers, cheap and certified first

```
NL description ──┬─────────────────────────────► bot writer ──► BotName.lean (compiles)
                 │                                                    │
                 └──► A1: expectation extractor (LLM, BLIND)          │
                          │  never sees the Lean                      │
                          ▼                                           ▼
                    predicted profile                    A2: outcome_prepass (CERTIFIED)
                    {CooperateBot: C, DefectBot: D, …}         actual profile
                                    │                                 │
                                    └────────► compare() ◄────────────┘
                                                   │
                        ┌──────────────────────────┼─────────────────────────┐
                        ▼                          ▼                         ▼
                 all cells agree            cell disagrees          cell undecided /
                 → `faithful`               → `mismatch`            phase-dependent /
                   (deterministic)            (deterministic,       structural claim
                                               actionable)                 │
                                                                           ▼
                                                                  Tier B judge agent
                                                              (ADVISORY — see §5)
```

### Why blind extraction is the load-bearing idea

A judge that reads the generated Lean **and** the description and rules "yes,
these match" is re-deriving the bot writer's own reasoning — same model family,
same blind spots, same text. It is correlated with the generator in exactly the
way that makes LLM judges fail, and the failure modes above are precisely the ones
where a plausible-sounding rationale reads fine.

Tier A1 breaks that correlation **by construction**: it turns the NL into a
behavioral prediction without ever seeing the artifact it checks. This is also the
only formulation that yields a defensible number for Phase-4 E2b ("behaves as
described") — the prediction must not be derived from the answer.

Tier A2 is **ground truth, not opinion**: every `determined` cell from
`outcomeG (guardFastN …)` is machine-certified equal to the classical `outcome`
via `outcomeG_sound ∘ guardFast_sound`. So the comparison is deterministic and
needs no judge calibration — a fact for the paper, not a vibe.

### Decisions this reverses

Both were made before `outcome_prepass.py` existed, which changed the economics
completely (certified behavior for pennies, no proof search):

- *"Reviewer is a workflow, not a second agent"* (`CLAUDE.md` Phase 3, design
  decision 2). Tier A1 **is** an agent — but only as blind input to a
  deterministic comparison, never as the arbiter.
- *"Reviewer workflow — deferred. Proof agent discovers outcome on its own; no
  separate prediction step needed."* The separate prediction step is the entire
  point: an outcome the proof agent discovered from the bot cannot check whether
  the bot matches the description.

## 3. Tier A1 — blind expectation extractor

`services/bot_expectation.py::extract_expectation`

**Blindness is structural, not a convention.** The signature takes
`strategy_description: str` — never a `BotResult`, never `lean_source`. There is a
test (`test_extractor_is_blind_by_signature`) asserting no such parameter can be
added, because the day it grows one, the comparison silently stops being
independent evidence.

Output is forced through a `submit_expectation` stop-tool (same discipline as
`verdicts.py` — never prose):

```python
ExpectedCell(opponent, my_action: "C"|"D"|"unspecified",
             confidence: "explicit"|"inferred", rationale)
Expectation(cells, structural_claims, summary)
```

Two fields carry most of the design weight:

- **`unspecified` is a first-class answer.** Most NL descriptions genuinely do not
  determine all four cells — *"cooperates with nice bots, punishes bullies"* says
  nothing about a perfect imitator. An extractor pressured into guessing
  manufactures false mismatches, which is the fastest way to make the reviewer
  ignorable. Unspecified cells are reported as coverage, never as failure.
  *Observed working:* on WaryBot's description the extractor answered
  `unspecified` for MirrorBot, citing the circularity.
- **`confidence`** separates *"the description literally says it defects against
  defectors"* (`explicit`) from *"a bot described as retaliatory presumably
  defects"* (`inferred`). Only `explicit` mismatches hard-fail individually;
  `inferred` ones warn. Without this split the false-positive rate is set by how
  aggressively the extractor extrapolates. **But see §5 — unanimity overrides.**

The prompt gives the four opponents' **behavior in words**, never `Program.lean`.
Handing it the language would push it to predict `Prog` terms and re-couple it to
the writer it is meant to check.

## 4. Tier A2 — certified behavioral profile

`services/bot_profile.py::build_profile`

Runs the prepass evaluator over the canonical opponents at `k ∈ {2, 4, 6, 16}` and
classifies each opponent into one cell verdict:

| Verdict | Meaning |
|---|---|
| `stable` | every determined budget agrees — `my_action` is meaningful |
| `phase_dependent` | determined budgets disagree — the full ladder is kept, `my_action` is `None` |
| `undetermined` | nothing committed (Löb boundary, cost floor, exotic guard, timeout) |

### The budget sweep is load-bearing

**The outcome is genuinely k-dependent.** Measured: `WaryBot vs DefectBot` is
`(C, D)` at k=2, 4, 6 and `(D, D)` at k=16 — the budget phase transition. A
reviewer sampling a single k reports a *budget artifact* as a faithfulness failure:
the description says "defects against defectors", you sample k=2, and a correct bot
fails.

So `phase_dependent` is a first-class verdict and is **never a mismatch on its
own** — "cooperates until it can prove otherwise, then defects" is frequently
exactly what the description meant. It routes to Tier B for interpretation.

Budget choice rationale, from 296 recorded prepass rows: **time is flat in k**
(~3 s/cell everywhere) and **memory is not monotone in k** (`WaryBot vs MirrorBot`
is determined at 2/4/8/16 but OOMs at 32). So raising the ceiling is cheap but does
not systematically determine more cells — the reason to sweep is the transition,
not coverage. k=6 samples between the 4 and 16 regimes where WaryBot's transition
lives. 32 is excluded as OOM-prone for reasons unrelated to k.

Cost: 4 opponents × 4 budgets ≈ **25–55 s per bot** at 2 workers.

### `staged_bot`

The profile must run **before** the human acceptance gate — that is the point of
showing it there — but `outcomeG` needs a real importable module. `staged_bot`
writes the source at its canonical path, yields the module name, then removes the
source **and its build artifacts** (a stale `.olean` would let a later import
succeed against dead code). It **refuses to touch an existing file**, so an
accepted library bot can never be clobbered — or, worse, deleted on context exit —
by a profiling run.

### Memory discipline — read before tuning

This project has lost a machine to unbounded `decFull` sweeps **three times**; the
2026-08-05 restart came from two concurrent sweeps × 4 workers × 3 GB.

- `jobs × memory_mb` is what the machine sees. `build_profile` **clamps `jobs`
  itself** to satisfy `MAX_TOTAL_MEMORY_MB`; a caller asking for 16 gets 2 and a
  warning.
- **`PROFILE_MEMORY_MB = 3072` is MEASURED, not chosen for comfort.**
  `WaryBot vs CooperateBot` at k=2 is `determined` at 3072 MB and dies with a
  `memory_exception` at 2560 MB. **Lowering the cap does not make the sweep safer
  — it silently converts determined cells into `undetermined`, which reads exactly
  like a genuine Löb boundary.** If memory is tight, cut `jobs`, never the cap.
- **Run sweeps sequentially.** Concurrent `build_profile` calls each clamp only
  themselves.
- Do not run live sweeps and the test suite concurrently: the tau module does
  `bots_dir.rglob("*.lean")`, and a staged file that vanishes mid-enumeration
  produces a spurious `FileNotFoundError` (observed 2026-08-05).

## 5. The comparison, and Tier B

### `compare()` — deterministic, nothing to calibrate

`bot_expectation.compare(expectation, profile) -> ReviewComparison`, with cells
classified `match | mismatch | unspecified | uncertified` and an overall verdict of
`faithful | mismatch | underdetermined`.

**Unanimity overrides confidence** (`unanimous_mismatch`). One `inferred` mismatch
is a warning — the extractor extrapolated, so it may have extrapolated wrong. But
if **every** certified cell (≥2) contradicts the description, no plausible reading
survives, and the verdict is `mismatch` regardless of individual confidence.

> **This was found by running a negative control, not by a unit test.** An
> inverted-polarity GuardianBot produced FOUR certified mismatches and still scored
> `faithful`, because each one alone was only `inferred`. Every unit test passed —
> they all encoded the rule as specified, and the specification was wrong at the
> aggregate level. Keep negative controls in the loop; they test the spec, not the
> code.

The `≥2` floor matters: a single lone inferred mismatch is exactly the weak
evidence the confidence split exists to discount.

### Tier B — the judge, on the residual only

`services/bot_judge.py::judge_residual`, fires only when `comparison.needs_judge`.

Its scope is what Tier A **cannot** decide: `uncertified` cells, `phase_dependent`
ladders, and `structural_claims` that behavior cannot separate (GuardianBot
punishes bullies via a frozen third-party probe; a direct-reciprocity bot could
produce an identical four-cell profile). Certified cells are passed as **settled
context and explicitly not re-litigated** — a judge able to overturn a machine
proof is a liability, and two tests assert settled cells never appear in the
open-questions section.

It gets **unfiltered** `read_library_file` / `search_library` (there is no answer to
leak: A2 already computed the behavior by proof). `underdetermined` is a
respectable verdict and the default when it fails — **a judge that errors must
never read as approval.**

> ### ⚠️ Tier B has NO ground truth
>
> Tier A2's cells are theorems. Tier B's verdict is an opinion, from a model in the
> same family as the one that wrote the bot. It is **advisory input to the human
> gate, never an acceptance criterion, and must not be reported in the paper as a
> verification result.**
>
> Observed (n=2, anecdotal): it correctly resolved WaryBot's phase-dependent
> ladder, citing `.neg (.plays .opp .self Action.C)` as evidence — good. On the
> inverted-polarity control it **named the inverted branch polarity in its notes
> and still returned `faithful`** — it saw the defect and did not let it change the
> verdict. Its top-level verdict is not reliable alone. This is exactly why Tier
> A's deterministic verdict governs.
>
> The honest experiment to quantify it: hand-label N generated bots, publish the
> judge's agreement rate against those labels. Until that exists, it is a hint.

## 6. Registry arity — the bug class, and the guard

`outcome_prepass.py` registered `"OptimBot {k}"` while
`Bots/LlmGenerations/OptimBot.lean` is `def OptimBot (kOpp kSelf : Nat) : Prog`.
Single-arg application elaborates to `Nat → Prog`, **not** a `Prog`, so `outcomeG`
yields nothing and every cell reads `undetermined`/`oom` — at every budget, against
every opponent — **indistinguishable from a genuine Löb boundary in the output.**
Confirmed by `#check`: `OptimBot 2 2 : Prog`, `OptimBot 2 : Nat → Prog`.

The guard: `arity_from_source` / `guard_from_source` / `bot_spec_from_source` derive
a spec from the bot's own `.lean` binder list, and `verify_registry_arity` (a test)
cross-checks all 18 registry entries. Reintroducing the bug fails three tests.
**Freshly generated bots must always go through `bot_spec_from_source` — never a
hand-written entry.**

Post-fix, OptimBot cells are still `undetermined`, but honestly so: it nests
`.search kSelf` inside `.search kOpp` and its docstring requires `kSelf` well above
`kOpp` for the rung-3 Löb bootstrap. The staggered shape (`OptimBot 2 64`) OOMs at
3 GB. Uniform `{k} {k}` is the right registry default; those cells are out of reach
of the fast decider for now.

**Known coverage limit:** `DupocBot` vs CooperateBot/DefectBot times out at 90 s
even pre-built and unstaged — a pre-existing property of the fast decider, not a
staging artifact. Coverage against searcher-heavy bots is patchier than the WaryBot
result suggests; those cells land in Tier B.

## 7. The rewriter loop — DESIGNED, NOT BUILT

Currently a mismatch is *reported* to the human, who decides. The rewriter closes
the loop: feed the discrepancy back to the bot writer and let it try again.

### Trigger

Only on evidence strong enough to act on automatically:

- `comparison.hard_failures` (explicit mismatches), or
- `comparison.unanimous_mismatch`.

**Not** on `inferred` warnings, `unspecified` cells, `uncertified` cells, or Tier B
verdicts alone. Rewriting on weak evidence turns a correct bot into a wrong one
chasing a bad prediction — and Tier B has no ground truth (§5), so it must never
drive an automatic code change.

### What the rewrite prompt may see

This is the subtle decision. The feedback message should carry:

- the original NL description (unchanged — it is the specification);
- the current Lean source;
- **only the mismatching cells**: opponent, expected action, certified action.

It must **not** carry the full certified profile. Handing over every cell invites
the writer to fit the four canonical opponents specifically rather than implement
the described strategy — overfitting to the test set, and the resulting bot would
pass the reviewer while being no more faithful. Report the failures, not the
answer key.

Tier B's discrepancies (`claim` / `expected` / `actual` / `evidence`) may be
included as *hints* when Tier A already triggered the rewrite, since the judge's
sub-term citations are genuinely useful for locating the error. They may never
trigger one.

### Termination

- **Max 2 rewrite attempts** per bot, then hand to the human regardless. The
  writer already iterates internally on compile errors; this is a second, outer
  loop and its cost is a full re-profile (~25–55 s) plus an extractor call per
  attempt.
- **The expectation is extracted ONCE** and reused across attempts. Re-extracting
  per attempt lets the prediction drift toward whatever the bot now does, which
  quietly destroys the independence the whole design rests on.
- **Stop early if a rewrite does not change the profile** — the writer did not
  understand the feedback, and a third identical attempt will not help.
- **Never auto-accept.** The human gate stays. The rewriter improves what is
  presented at the gate; it does not replace the gate.

### Regression risk

A rewrite fixing cell X may break cell Y. Since the expectation is fixed, the
comparison is directly comparable across attempts: keep the attempt with the
fewest hard failures, ties broken by the earlier attempt, and **show the human the
history**, not only the final version. A bot that oscillated is a signal the
description is ambiguous — which is a finding about the description, not a defect
in the bot.

### Sketch

```python
def rewrite_until_faithful(name, description, initial, *, max_attempts=2):
    expectation = extract_expectation(description)       # ONCE
    attempts = [_evaluate(name, initial, expectation)]
    while len(attempts) <= max_attempts and attempts[-1].comparison.should_rewrite:
        nxt = search_bot(BotRequest(..., feedback=_mismatch_brief(attempts[-1])))
        ev = _evaluate(name, nxt, expectation)
        if ev.profile.behavior_key() == attempts[-1].profile.behavior_key():
            break                                        # no behavioral change
        attempts.append(ev)
    return min(attempts, key=lambda a: len(a.comparison.hard_failures)), attempts
```

### Prerequisites — ALL BUILT (2026-08-05)

The loop itself is still unwritten, but everything it needs now exists:

1. ✅ **`BotRequest.feedback: str | None`** + the `feedback` parameter on
   `prompts.bot_request_message`, carrying the mismatch brief into the writer's
   opening user turn as a "THIS IS A REWRITE" block. The block restates the
   description as the unchanged specification, tells the writer **not** to
   special-case the named opponents, and lists the common causes (frozen `.bot X`
   vs `.opp`, `.self`/`.opp` swapped, branches exchanged).
2. ✅ **`ReviewComparison.should_rewrite`** — `hard_failures or
   unanimous_mismatch`. THE single place the "never rewrite on weak evidence"
   rule lives; tests assert it does **not** fire on a lone `inferred` mismatch,
   an `unspecified` cell, or an `uncertified` cell. Paired with
   **`mismatch_brief()`**, which emits only the FAILING cells — a test asserts
   passing cells never leak into it.
3. ✅ **`BotProfile.behavior_key()`** — built first, because the trap it avoids is
   silent. **Do NOT use `profile_a == profile_b`** to ask whether behavior
   changed: `raw` holds `CellResult`s carrying per-cell wall-clock `seconds`, so
   two behaviorally identical profiles compare **unequal** (verified: `a == b` is
   `False` while `a.cells == b.cells` is `True`). A stop-early guard written
   against `==` never fires, and every rewrite silently burns the full attempt
   budget.
4. ✅ **`evaluate_against(name, source, expectation, ...)`** — `review_bot` minus
   the extraction step, so the expectation can be **injected**. `review_bot` now
   calls it. A test asserts `evaluate_against` has no `strategy_description`
   parameter: it must be structurally unable to extract its own expectation,
   which makes "extract once" enforceable rather than a convention.
5. ✅ **`persist_review(...)`** — one JSONL row per attempt under
   `generated/reviews/<bot>_<ts>.jsonl` (attempts of a run share a file via
   `run_ts`), mirroring `generated/outcomes/`. Records the source, verdict,
   `should_rewrite`, coverage, `behavior_key`, the full expectation and
   per-cell comparison, and an optional judge payload — the longitudinal data
   E2 needs to answer "did rewriting help, and did anything oscillate?".

### The loop — BUILT (`services/bot_rewriter.py`)

`rewrite_until_faithful(...) -> RewriteRun`, returning every `Attempt` plus the
selected one. Termination: `faithful` | `max_attempts` | `no_behavior_change` |
`writer_failed`. Selection is fewest hard failures, **ties to the earlier
attempt** — a rewrite must earn its place, since the initial bot was written
against the full description while a rewrite sees only a mismatch list.
`RewriteRun.oscillated` flags behavior returning to an earlier state, which is a
finding about the DESCRIPTION (it is ambiguous about the disputed cells), not a
defect in the bot.

## 7b. Where it is exposed

The reviewer and rewriter are reachable from both front ends:

| Surface | Control | Default |
|---|---|---|
| `run_bot_pipeline` CLI | `--max-rewrites N`, `--no-review` | 2 rewrites, review on |
| Web app (`pd-serve`) | "Faithfulness" dropdown: *review + auto-rewrite* / *review only* / *off* | review + auto-rewrite |
| API | `PipelineRequest.review_bots`, `PipelineRequest.max_rewrites` | `True`, `2` |

The web flow runs the review **between** bot generation and the `bots_ready`
gate, so the human sees the verdict, the per-opponent cells, the rewrite history,
and the (clearly-labelled advisory) judge line next to the source they are
accepting. `BotDraft.review` carries it; `bot_rewriter.review_payload()` builds it
so the CLI and the app cannot drift about what a review *is*.

Reviews are **sequential, never concurrent** — each runs a certified Lean sweep,
and `jobs × memory_mb` is what the machine sees (§4). A review or judge failure is
non-fatal and logged: the pipeline must not die because an advisory check broke.
Prove-only mode hides the control entirely (both bots come from the library, so
there is no description to check against).

**Still not done:** nothing auto-accepts. The human gate is unchanged — the
rewriter only improves and annotates what reaches it.

## 8. E2 harness — the paper number

Phase-4 experiment E2 wants 10–20 NL descriptions measured on: (a) compiles,
(b) behaves as described against the canonical opponents, (c) full pipeline
end-to-end. Everything it needs now exists.

`eval/run_bot_eval.py`, non-interactive, one JSONL row per description:

```
description → search_bot → compiles?
            → extract_expectation (blind)  ─┐
            → build_profile (certified)    ─┴→ compare → verdict + per-cell detail
            → judge_residual if needed
```

Report: compile rate; **faithfulness rate over cells the evaluator certified**
(state coverage explicitly — an uncertified cell is not a pass); count of
`phase_dependent` cells; and Tier B's verdicts **separately and clearly labelled
as advisory**, never folded into the headline number.

Mix paraphrases of existing bots (where the intended answer is known) with genuinely
new strategies. The paraphrase subset doubles as the hand-labelled set for
quantifying Tier B (§5).

## 9. Open conventions

Still unsettled; decide before extending:

1. **Canonical opponent set.** `CLAUDE.md` fixes four, and all four are search-free
   — which is what keeps the expensive both-searcher regime out of scope. WaryBot
   and GuardianBot arguably need a searcher opponent (DupocBot) to show their
   character, but that reopens the infeasible regime. *Proposed: keep four for v1,
   document the limitation.*
2. **`inferred` mismatch severity.** Currently warn-only individually, fail on
   unanimity. Should a 3-of-4 inferred mismatch fail? *Proposed: no — unanimity is
   the honest threshold, and lowering it re-imports the false-positive problem.*
3. **Reporting a phase-dependent cell to the human.** *Proposed: always show the
   whole ladder, never collapse it to one k.*
4. **Whether the rewriter may see Tier B's discrepancies** as hints. *Proposed:
   yes as hints once Tier A has triggered, never as a trigger (§7).*

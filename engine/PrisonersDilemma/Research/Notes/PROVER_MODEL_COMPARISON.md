# Prover-model comparisons on the OSGT engine (E4 evidence)

Longitudinal case studies of different LLMs driving the SAME proof-agent harness
(`app/`: episode loop, notebook memory, structured verdicts, Lean tools) on the
same theorems. This is the evidence base for Phase-4 experiment **E4** (SOTA /
open-model baseline): the paper's claim is not "Claude beats X at Lean syntax"
but that the domain gap lives in **metatheoretic judgment** and **verdict
discipline**, which competition-math-trained provers don't exercise.

Add one section per comparison; keep the raw-artifact pointers — the
`generated/outcomes/` directories are never deleted.

---

## Case study 1 — DIMCID vs CupodBot: claude-opus-4-8 vs leanstral-1-5 (2026-08-05)

**The matchup.** `DIMCID k` (`.impl`-guard searcher: "if I play C vs you then you
play D vs me" → then D, else C) vs `CupodBot k` (plays-guard searcher: "you play
D vs me" → then D, else C). Both-searcher, mutually entangled guards — the hard
regime. Semantically the outcome is **(C, C)** (both guards consistently false,
both fall to else), but no current proof-system route certifies it.

**Setup.** Identical harness and budgets both runs: `max_episodes=3`,
`max_turns_per_episode=10` (+1 reminder turn each episode → 20–21 turns at cap),
same tools (`run_lean_proof`, `read_library_file`, `search_library`,
`update_notebook`, `submit_verdict`), same leak guards. Only `--model` differs.
Claude ran 2026-07-31, leanstral 2026-08-05 via the OpenAI-compat client
(`llm/openai_client.py`, Mistral free endpoint) — leanstral's first hard live
outing on this pipeline.

### Results

| | claude-opus-4-8 | leanstral-1-5 |
|---|---|---|
| Verdict | `open_blocked`, outcome (C,C) — submitted ep1 turn 9, re-derived and confirmed by the open-verdict retry episode | **none in 62 turns** — 3× `turn_cap`, run exhausted |
| Wall-clock | **16 min** (6 + 10) | **358 min** (65 + 112 + 181) |
| Turns | 19 | 62 |
| Compiles | **11/11 green** (compiles used as probes/verification) | **3/34 green**, and the 3 are `#eval` size-probe scratches |
| Compile errors | — | 12 unsolved goals, 5 type mismatch, 3 syntax |
| Output tokens | 39,326 | 605,106 |
| Uncached input | ~40 | 4,068,528 (cache_creation = 0 throughout) |
| Cost | $3.97 | $0 (free endpoint) |
| Best-attempt `.lean` | 39-line wall-verification file (mutual_pblt shape checked and refuted in comments) | 16-line `#eval` size probe |
| Tool fidelity | clean | hallucinated `write_lean_proof` once (recovered from the error string) |

Artifacts: `app/generated/outcomes/DIMCID_vs_CupodBot_20260731T160204/` (Claude),
`app/generated/outcomes/DIMCID_vs_CupodBot_20260805T113616/` (leanstral).

### The substance gap is smaller than the outcome gap

**Leanstral's semantic reasoning was correct.** It hypothesized (C,C), identified
both guards as circular, and discovered real library facts the hard way: cost is
an INDEX on `PlaysProof`, not a stored field; `c_guard k = numCost k = log₂ k + 1`;
the `searchBranch` implication shape; which existing proofs use
`no_provable_searcherPlay_tail` vs WV censuses. Its ep2 notebook is a competent
lab record of failed tactic routes. This is *not* a model that can't read Lean.

**Claude went three levels deeper — to the walls.** Its final notebook is a
precise unprovability analysis, cross-checked twice (the retry episode re-derived
it from scratch):

- **Legs:** L1 (Cupod, searchBranch): `□_k B → A`; L2 (DIMCID): `□_k guard → B`;
  L3: `A → guard` (implK). With `B` = "DIMCID plays D", `A` = "Cupod plays D",
  `guard = P → A`, `P` = "DIMCID plays C".
- **(D,D) walled by the guard-box subscript:** `mutual_loeb`/`mutual_pblt` need
  `□_k A → B`; boxing L3 via axK forces a budget `c > k`, but DIMCID reads its
  guard box ONLY at exactly `k` (searchBranch subscript = search budget), and
  downward boxMono is unsound. No diag/bloeb route either: `B → □_k B` needs a
  certificate of `B`, which is the open question itself.
- **(C,C) census walled:** WV valuations can only force C-atoms TRUE; they cannot
  force D-atoms FALSE. The undischargeable obligation is `search_t` (hypothesis
  `WV S guard`, need `False`). This is the **dual of the WaryBot `.neg`-guard
  case** — a forced-false THEN-play D-atom, which no existing valuation/floor
  kernel handles.
- **No size floor:** both guards are O(log k) ≪ k, so `proofSearch_false_*_undersized`
  never applies at large k.
- **Consistency of the entanglement:** `interp A → interp B` holds (Cupod's guard
  fires + Pf_sound) but NOT conversely — DIMCID playing D makes `P` false, so its
  guard is vacuously true and yields no `interp A`. The loop breaks at DIMCID
  (asymmetric), so there is no contradiction to mine, hence genuinely
  `open_blocked` rather than a provable census. Not bistable: eval is
  deterministic and both guards are semantically false.

**The sharpest single detail.** Leanstral's final plan was mutual strong
induction on the budget, and its notebook ends MID-SENTENCE (see §harness,
truncation):

> *"The key missing piece: extracting a PlaysProof at smaller budget from a giv"*

That missing piece **is the wall**: `search_t` cites the fired guard at
`c_guard k` (log-sized), not at `k`, so there is no strict budget descent to
induct on — the same design fact recorded in the `searchThenSearch_t` dead-end
note ("cite via c_guard"). Leanstral was one insight away from the right
conclusion but framed the wall as an engineering gap to solve next episode.
Claude recognized that failing-for-a-reason IS the result. That is the
research-judgment gap, and it is not a Lean-syntax gap.

### Harness findings (actionable, OpenAI-compat path)

1. **Verdict discipline failed.** 62 turns, believing (C,C) and unable to prove
   it, leanstral never called `submit_verdict`. The per-turn reminder fired and
   was ignored. Proposal: after N ignored reminders, offer a final turn where
   `submit_verdict` is the ONLY registered tool.
2. **The 4000-char notebook cap truncated the run's most important sentence**
   (the quote above — ep2's notebook is exactly 4000 chars). Silent truncation of
   replace-whole-text is the wrong failure mode; bounce an over-cap write back to
   the model ("shorten this") instead.
3. **ep3 never updated the notebook** (0 `update_notebook` calls; ep3's notebook
   is byte-identical to ep2's). The forced end-of-episode reflection either did
   not fire or was not complied with — audit that mirror in
   `llm/openai_client.py` (episode semantics are supposed to be 1:1 with
   `client.py`).
4. **One hallucinated tool name** (`write_lean_proof`); the error string was
   enough to recover. Cosmetic, but worth counting in E4 metrics.

Bookkeeping: despite TWO `open_blocked` verdicts from the Claude run, the pair is
**not recorded in `app/outcome_status.toml`** — the open-verdict → status-record
path goes through a human confirm gate that was never clicked. Add it manually if
the matrix should show it.

### Paper take (E4)

A Lean-community open model with full tools, library search, and episode memory
reproduces the *semantic* analysis of a hard cell but lacks (a) the metatheoretic
judgment to recognize an unprovability wall as a result, and (b) the verdict
discipline to report one — at 22× the wall-clock. This is a sharper justification
for the bespoke pipeline than a raw pass-rate table: the bottleneck the pipeline
addresses is not tactic generation, it is knowing *when the right answer is
"blocked, and here is the wall"*. (Caveat for honesty: n=1 matchup, and the
matchup was selected precisely because it is wall-shaped. Balance E4 with cells
where a proof exists.)

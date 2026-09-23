# Transparency analysis — handover

**Written for: a collaborator joining the transparency/EGT analysis, who has not
seen this repo before.**

The question this data answers: **how much transparency does Löbian cooperation
need?** Agents here can read each other's source and prove things about it. We
blur that visibility along a dial `t` (1 = full transparency, 0 = opaque), drop
the resulting population into evolutionary dynamics, and ask where cooperation
survives.

Your job for the first pass: **find interesting dynamics and results in the
data.** Not to reproduce ours. Please read §4 before §5 — I want your own read
first, and §5 is deliberately the second step.

---

## 1. Setup (~5 minutes)

```bash
cd app
uv sync
```

Python ≥3.11. That is the whole setup for analysis work:

- **No API key needed.** None of the analysis modules import `anthropic`.
- **No Lean build needed.** The matrix cells are pre-exported to
  `app/generated/outcome_theorems.json` and `app/generated/tau_rows.json`, both
  committed.
- Always `uv`, never `pip` (`uv run …`, `uv add …`).

Optional: `lrsnash` is a secondary Nash cross-check solver, a conda-forge binary
`uv` cannot install. It is absent in all 94 runs and the pipeline records that
honestly rather than pretending the check passed. Ignore it.

Verify your setup:

```bash
uv run python -m pd_runner.egt.integrity ../app/generated/egt
```

Expect `VERDICT: CLEAN`, 0 hard failures, 1 soft finding (the `lrsnash` note).

---

## 2. Where the data is

Everything lives under `app/generated/egt/`.

**The data is `runs/<zoo>_<family>_t<NNN>_a<NNN>_<hash>/` — 94 run directories,**
one per distinct analysed matrix. Each holds the output of the six analysis
stages: `summary.json` (headline metrics for every stage), `ess/`, `invasion/`,
`faces/`, `nash/`, `replicator/`, `moran/`.

A curated slice of each run is committed — the summaries, payoff matrices, Moran
stationary distributions, Nash equilibria and per-stage assumptions. The bulk
output (parquet face tables, invasion graph renders, replicator basins) is not in
git: it is reproducible, and a full regeneration of the sweeps is ~3 h.

**There is deliberately no derived analysis layer in the repo.** No tidy table,
no figures, no findings document. The tracked slice is exactly the input the
analysis modules consume, and they build that layer in seconds — so the first
cut should be yours, not a copy of ours. Build it whenever you want it:

```bash
cd app
uv run python -m pd_runner.egt.analysis        ../app/generated/egt
uv run python -m pd_runner.egt.findings        ../app/generated/egt
uv run python -m pd_runner.egt.nash_structure  ../app/generated/egt
```

That writes `analysis/` (gitignored): `tidy.csv` — one row per (zoo, family, t,
α), 216 rows — plus phase maps, family diffs, a Moran drill-down, a Nash
component table and six figures.

**Treat those modules as a starting point, not the API.** They encode the
questions we happened to ask. `tidy.csv` flattens `summary.json` and drops a
lot; the run directories hold more than it exposes. Reading
`pd_runner/egt/analysis.py` (~140 lines) shows what is being thrown away, and
writing your own loader over `runs/*/summary.json` is entirely reasonable — that
is where a different question gets asked.

---

## 3. Reading the table

**The two dials — never conflate them:**

- **`t`** = transparency. A property of the *signal*: how well an agent can tell
  which opponent it faces. Grid: `{0, 0.2, 0.4, 0.6, 0.8, 1.0}`, normalized
  mutual information.
- **`α`** = the agent's own caution threshold — how much probability mass must
  provably cooperate before it will. Grid: `{0, 0.3, 0.45, 0.62, 0.8, 1.0}`.

**`zoo`** — which bots are in the population:

| zoo | n | what it is for |
|---|---|---|
| `body` | 10 | the headline zoo, twin-free, fully proven |
| `body+twins` | 12 | adds two behavioral twins that are syntactically far apart — for the behavioral-vs-syntactic comparison, never headline curves |
| `body+twins+natives` | 14 | adds two native aggregator players (max, min) over the same test — the {sum, max, min} ablation |

**`family`** — what leaks and how it blurs. All three are calibrated to the same
`t`, so at matched `t` the information *rate* is identical and only the
*confusion structure* differs:

- **`behavioral`** — softmax over Hamming distance between action rows. The
  Bayes posterior of watching every match through a noisy channel. "I watched
  it play."
- **`syntactic`** — softmax over AST tree-edit distance. Degraded *source*
  access. Its confusion structure **inverts** the behavioral one (two bots can
  share a tree shape but behave oppositely).
- **`epsilon`** — `(1-ε)·δ + ε·uniform`. The null control: no similarity
  structure, everything equally confusable. Identity-based, so no twin ceiling.

Six (zoo, family) combinations × 36 grid points = 216 rows.

**The analysis stages behind the columns:** pure ESS → invasion graphs → face
equilibria → extreme Nash (what *exists*), then replicator basins → Moran
fixation (where a population actually *goes*).

---

## 4. Your first pass

Build your own view of the data before reading ours. Concretely: run the three
commands in §2 (or write your own loader), get a table you trust, and look.

Some honest entry points — none of them is the "intended" answer:

- **Where does cooperation die?** Walk `t` downward at fixed `α` and find where
  the cooperative outcome stops being selected. Is the boundary sharp or gradual?
  Does it differ per `α`?
- **Does confusion structure matter, or only rate?** Compare `behavioral` vs
  `syntactic` vs `epsilon` at matched `t`. They carry identical information;
  any difference is structurally caused. This is the comparison I find most
  interesting and least explored.
- **Does caution help or hurt?** `α` is the agent's own parameter. There is no
  a priori reason more caution is better.
- **What do the twins do?** Behaviorally identical, syntactically distant bots
  should be separable under one family and not the other.
- **Aggregators.** `body+twins+natives` on `epsilon` varies only how a bot
  aggregates evidence (sum vs max vs min) — ambiguity aversion versus
  ambiguity seeking.

**Five traps, learned the hard way — these are real, not hedging:**

1. **α = 0 is degenerate.** `≥ 0` makes every agent an unconditional
   cooperator, so that corner is the all-C matrix, not a result. Exclude it from
   every claim.
2. **Population share ≠ cooperation.** At low `t` the Löbian types survive *as
   defectors*. A share curve is not a cooperation curve. The comparable
   quantity is `Σ share(i)·[i's self-cell is (C,C)]`. This mistake was actually
   made and caught here — the share curve visibly exceeded the static ceiling.
3. **"Uniquely stochastically stable" is a strong-selection claim.** It means
   M=100, β=1. Robustness across the nine (M, β) combinations is typically 6/9.
   Always carry the qualifier.
4. **Extreme-NE vertex counts are polytope geometry, not strategy content**
   (they go 21 → 8 → 121 non-monotonically). Use component counts and their
   cooperation classification instead.
5. **Report per phase region, not per grid point.** The (t, α) diagram is
   piecewise constant; points sharing a matrix fingerprint are provably the same
   analysis. `grid_points` in each run summary records the dedup.

Non-convergence is a finding, not a failure — it is counted, never assigned to
an attractor.

---

## 5. Second step — only after your own pass

Once you have formed a view, these say what we already think, and what we think
is shaky. Reading them first would cost the main thing you are here for: an
independent read.

- `engine/PrisonersDilemma/Research/Notes/EGT_FINDINGS.md` — the results-section
  record: findings F1–F7, each with an evidence pointer, plus conventions and
  open questions. Its pointers name files under `analysis/` — the same ones your
  §2 rebuild produces. **Corrected 2026-09-15:** F1 previously claimed no pure
  ESS anywhere; the true count is 93 of 94 matrices (the exception is EBot at
  `body`/syntactic, t=0.2, α=0.8). If you find other overstated claims, that is
  a useful result in itself.
- `engine/PrisonersDilemma/Research/Notes/TAUBOTS.md` — the transparency layer's
  design: what the lift *is*, what was rejected and why.
- `app/generated/tau_report_{body,twins,natives}.html` — per-zoo interactive
  reports (8–11 MB, open in a browser).

Where a note and the data disagree, **the data wins** — tell me.

---

## 6. Caveats to carry into anything you write

- The `critch8` zoo was never swept; it is outside every count here.
- Nash cross-check absent in 94/94 runs (`lrsnash` missing) — a limitations
  sentence, not a defect.
- A swept matrix never contains the non-termination state: the transparency lift
  always terminates, so a proven-`none` base cell reads as a real `D`. Compare
  base-matrix and swept results only with this in mind.
- Basins group by *support*, not proximity — the endpoints lie on a neutrally
  stable continuum, and clustering by distance would report dozens of spurious
  attractors.

---

*Questions: ask me directly. The fastest way to be useful is to disagree with
something in §5 using something in §2.*

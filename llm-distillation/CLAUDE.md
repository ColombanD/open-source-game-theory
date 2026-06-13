# llm-distillation — convex-hull profile fitting

Fit a model's **per-opponent cooperation profile** to the convex hull of a
library of reference strategies, and report the best fit under several distances.

## The data

[`data/payoff_matrix.csv`](data/payoff_matrix.csv) is a square, fully populated
matrix for a two-player, two-action game with actions in `{C, D}`. Cell
`(row A, column B)` encodes a **pair** `(row_action, col_action)`:

- the action the **row** bot plays against the column bot, and
- the action the **column** bot plays against the row bot.

The shipped cells look like `"(C, D)"`. The parser
([`parse_cell`](src/distillation/data.py)) also accepts `"C,D"`, `"CD"`, and
spacing variants, but the canonical encoding here is `"(C, D)"`.

### Conventions (fixed everywhere in the codebase)

- **`C → 1`, `D → 0`** — cooperation is probability 1, defection is 0. Used for
  the reference matrix, the input vector, and every output.
- **Canonical bot ordering** = the CSV's row order. The current library has
  `N = 8` bots: `CooperateBot, CupodBot, DBot, DefectBot, DupocBot, OBot,
  TitForTatBot, EBot`. This ordering is reused for every vector, matrix, and
  report. The bot set is the unique bots in the matrix; the loader checks that
  the row order matches the column order.

### Reference vectors — row's own action, **no transpose**

For bot `i`, the reference vector `r_i` is **row `i`'s own action against every
opponent** — i.e. the **first** element of the pair in cell `(i, j)` for all `j`.
This is "what bot `i` does against each opponent". The second (column-action)
half of each pair is **never used** and we **never transpose**.

`R` is the `N × N` matrix whose row `i` is `r_i` (rows = bots, columns =
opponents, entries in `{0, 1}`). The CLI prints `R` so it can be eyeballed
against the source CSV.

> Note: the shipped matrix genuinely contains **identical rows** (CupodBot and
> DupocBot have the same reference vector) and **identical columns** (the
> CupodBot and OBot columns coincide; so do the DupocBot and TitForTat columns).
> The first makes some weight fits non-identifiable; the second makes certain
> inputs provably off-hull. Both are exercised in the tests.

## What the tool computes

You provide an input vector `x ∈ [0,1]^N`, where `x_i` is the probability that a
new model plays `C` against reference bot `i` (canonical order). We find the
convex combination of reference rows closest to `x`:

> with `w` on the simplex (`w_i ≥ 0`, `Σ w_i = 1`), the fitted profile is
> `Rᵀ w`, and the realizable set is `conv{r_i}`.

### Distances implemented ([`fitting.py`](src/distillation/fitting.py))

| Metric | Problem | Solver |
|---|---|---|
| **L2** | `min ‖Rᵀw − x‖₂` over the simplex | convex QP, `scipy.optimize.minimize` (SLSQP). Fitted point is **unique**. |
| **L1** | `min ‖Rᵀw − x‖₁` | LP with per-coordinate auxiliary variables for the absolute values, `scipy.optimize.linprog`. |
| **L∞** | `min ‖Rᵀw − x‖∞` | LP with a single slack bounding every coordinate's deviation. Minimises the **worst** per-opponent miss — a different question than L1/L2, hence included. |
| **ExpectedHamming** | `min Σ_j [p_j(1−x_j) + (1−p_j)x_j]` with `p = Rᵀw` | LP. This is **linear** in `w`, so the optimum sits at a simplex **vertex**: it reduces to "pick the single library bot nearest `x` in expected Hamming". Reported as a cheap nearest-bot baseline, not a true hull fit. |

We deliberately use real QP/LP solvers (no hand-rolled gradient descent).

### Reported quantities (per distance)

- **Fitted profile** `Rᵀ w*` next to the input `x`, coordinate by coordinate.
- **Optimal weights** `w*`, listing only bots with non-negligible mass, by name.
- **Residual** `‖Rᵀ w* − x‖` in that metric. A **nonzero residual means no convex
  combination of library bots can reproduce `x`** — it sits off the library
  manifold (outside `conv{r_i}`).
- **Identifiability**: whether the active (positive-weight) reference rows are
  **affinely independent**. If not, the **fitted point is still unique but the
  weights are not** — mass can be shuffled among the dependent rows. The simplest
  case is two identical active rows, where mass splits arbitrarily between them
  with no effect on the fit. (Checked via the rank of row differences.)

### Reported once (metric-independent, from `x` directly)

- **`level = mean(x)`** — overall cooperativeness.
- **`sharpness = mean(|x_i − 0.5|)`** — how decisive (near 0/1) the profile is.

## LLM distillation pipeline

The above fits a cooperation vector `x` that you supply by hand. The pipeline
*measures* `x` for a real LLM and then runs that fit automatically.

**What it does.** For each bot in the library (canonical CSV order) the model is
queried, in a one-shot **maximum-transparency** (source-visible) prisoner's
dilemma, against that bot. A hardcoded **Python-pseudocode** description of the
bot (`src/distillation/bot_descriptions.py`, `BOT_DESCRIPTIONS`) is injected into
the prompt — not the actual Lean source, so the model reasons about the strategy
rather than the engine syntax. Each bot is queried `N` times; the fraction of `C`
replies is the Bernoulli estimate `x_i = P(model plays C against bot i)`. The
full `x` then goes straight into the existing `fit_all` + `format_report` — the
model is treated as "a new bot" whose row is measured rather than read from the
CSV (same C=1/D=0, no-transpose convention). `BOT_DESCRIPTIONS` must cover every
bot in the matrix.

**Default `N = 30`.** For a Bernoulli proportion the 95% CI half-width is
`≈ 0.98/√N`, so `N = 30` gives `≈ ±0.18` at the worst case `p = 0.5` — a fair
estimate at modest cost (`N × 9` calls). Raise `N` for tighter estimates.

**Temperature defaults to `1.0`** — sampling must be stochastic, or every query
returns the same action and `x_i` collapses to exactly 0/1.

**API.** Calls go through the OpenAI SDK pointed at OpenRouter
(`https://openrouter.ai/api/v1`). Set `OPENROUTER_API_KEY` in the environment.

The prompt (`src/distillation/prompt.py`, `PROMPT_TEMPLATE`) frames the game,
explains the source-code helpers the model will encounter (`simulate`,
`proof_search`, the budget `k`, probe-bot references), and asks the model to
reason and then end with a `My action <<A>>` line. `parse_action`
(`openrouter.py`) extracts `A` from that marker (last occurrence wins); a reply
with no marker parses to `None` and is dropped from the estimate.

**Output.** Each run creates `runs/<YYYY-MM-DD_HH-MM-SS>_<model-slug>/` with:
- `metadata.json` — model, n, temperature, timestamp, matrix path, bot order.
- `raw_responses.json` — every raw reply + parsed action, per bot.
- `cooperation_vector.json` — the measured `x` (ordered list + by-bot map).
- `report.txt` — the `format_report` fit output.

**Run it:**

```bash
conda activate py-random
export OPENROUTER_API_KEY=...
distillation-llm --model anthropic/claude-3.5-sonnet            # N=30 default
distillation-llm --model openai/gpt-4o --n 100 --temperature 1.0
```

Flags: `--model` (required), `--n`, `--temperature`, `--matrix`,
`--output-root` (default `runs`).

## Layout

```
src/distillation/
  data.py          # CSV parsing, reference matrix R, input-vector loading
  fitting.py       # L2/L1/L∞/ExpectedHamming fits, identifiability, profile stats
  reporting.py     # human-readable report formatting
  cli.py           # argparse entry point (manual-vector fit)
  bot_descriptions.py  # hardcoded Python-pseudocode descriptions of the bots
  prompt.py        # per-bot prompt construction (game framing + notation)
  openrouter.py    # OpenAI-SDK client for OpenRouter + `My action <<A>>` parsing
  pipeline.py      # measure x via the LLM, fit, write run folder
  pipeline_cli.py  # `distillation-llm` entry point
tests/             # parsing + fitting tests
data/payoff_matrix.csv
runs/              # per-run outputs (created at runtime)
```

## Running

This project uses the conda environment **`py-random`** (Python 3.11, with
`numpy`, `scipy`, `pytest`). Activate it first:

```bash
conda activate py-random
```

Install (editable) or just run via the source tree:

```bash
pip install -e .                 # provides the `distillation` console command
# or, without installing:
PYTHONPATH=src python -m distillation ...
```

### Examples

```bash
# Inline C/D string (C=1, D=0), all distances:
distillation data/payoff_matrix.csv "CDCDCDCC"

# Floats, restricted to two metrics, suppress the R printout:
distillation --no-matrix --metric L2 --metric L1 \
    data/payoff_matrix.csv "1,1,1,1,1,0,1,1"

# Input from a file (JSON list, CSV floats, or a C/D string all work):
distillation data/payoff_matrix.csv my_profile.json
```

The input vector accepts: an inline C/D string (`"CDCC"`), inline
comma/space-separated floats, or a path to a file containing JSON
(`[1.0, 0.0, ...]`), CSV/whitespace floats, or a C/D string. Length must equal
`N`, and entries must lie in `[0, 1]`.

## Tests

```bash
conda activate py-random
python -m pytest            # from the project root
```

Coverage:

- **Parsing** — a tiny synthetic matrix parses to the correct `R` with no
  transpose error; `C/D → 1/0` is correct; non-square and row/column-mismatch
  matrices are rejected; input-vector loaders (C/D string, JSON, CSV floats,
  length/range validation).
- **Exact-vertex recovery** — `x = r_k` ⇒ weight concentrated on bot `k`,
  residual ≈ 0, under every metric.
- **Interior point** — `x = ½r_a + ½r_b` ⇒ residual ≈ 0 with mass on `{a, b}`
  (asserted on the fitted point, since weights may be non-unique).
- **Off-hull** — an `x` provably outside the hull yields a strictly positive
  residual; the L2 residual is sanity-checked against a brute-force simplex grid
  projection.
- **Coincident rows** — two identical rows ⇒ weights reported as **not
  identified** (mass may split between them) while the fitted point and residual
  are well-defined.
- **Solver agreement** — L1/L2 fitted points stay in `[0,1]^N`, sum-to-one
  weights, and agree on realizable points.

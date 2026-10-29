# `app/` — `pd_runner`, the Python core

The deterministic half of the project: it reads the two Lean exports and computes the paper's
tables, figures and experiments. It never reads Lean source. The LLM pipeline (bots from natural
language, the proof agent, the web UI) is the separate [`../pipeline/`](../pipeline/) project, which
depends on this one.

## What is here

| Package | What it does |
|---|---|
| `eval/outcome_matrix.py` | Loads a matrix from an export (`source="sprime"`, the default, or `"engine"`), applies the floor policy, renders TSV/Markdown, diffs the two sources (`eval/source_diff.py`), and curates the open cells of the engine matrix (`outcome_status.toml`). |
| `eval/sprime_floors.py` | The `S'` floor dichotomies: the hinge-side pairs for the robustness check. |
| `tau/` | Partial transparency: `matrix.py` (zoos, `TauMatrix`, the kernel-row backing), `signal.py` / `channels.py` (the σ-families over behavioral and syntactic distances), `play.py`, `sweep.py`, `def4_theorems.py` (the exported tau rows), `compare.py` (Def 3 ≡ Def 4 certification), `report.py` (the HTML report). |
| `egt/` | Evolutionary analysis of a matrix: `static_analysis/` (ESS), `invasion/` (graphs, SCCs), `faces/` (face equilibria), `nash/` (extreme NE), `replicator/` (basins), `moran/` (fixation, stochastic stability); `pipeline.py` runs a `(t, α)` sweep, `report.py` renders it. |
| `settings.py` | `CELL_SOURCE` (`PD_CELL_SOURCE`, default `sprime`) and `FLOOR_POLICY` (`PD_FLOOR_POLICY`: `engine_side` default, `restrict_zoo`, `hinge_side`). |
| `generated/` | The exports (`sprime_outcome_theorems.json`, `sprime_tau_rows.json`, `outcome_theorems.json`, `tau_rows.json`), `source_diff.md`, and the EGT sweep output (`egt/runs/`, gitignored). |

## Quick start

```bash
cd app
uv sync --extra dev
uv run pytest

uv run python -m pd_runner.eval.outcome_matrix                       # the matrix (S', TSV)
uv run python -m pd_runner.eval.outcome_matrix --source engine       # the engine's S for comparison
uv run python -m pd_runner.eval.source_diff                          # S vs S' diff report
uv run python -m pd_runner.tau.compare --zoo paper --source sprime   # Def 3 ≡ Def 4 certification
uv run python -m pd_runner.egt.pipeline --zoo body8 --t-steps 6      # a (t, α) sweep
```

The paper's tables and figures are generated from here by the scripts in `../latex/scripts/`.

## Refreshing the exports

```bash
(cd ../arith  && lake build && lake exe export_sprime_outcomes)   # S' cells, floors and tau rows
(cd ../engine && lake build && lake exe export_outcomes)          # the engine's cells and tau rows
```

Both files are digest-protected; the loaders refuse an export whose digest does not match its
rows. When an export is absent in a checkout, the test suite points the `sprime` loaders at the
committed samples in `tests/fixtures/` (see `tests/conftest.py`).

## Conventions

* Every loader takes `source=` and `floor_policy=`; a `S'` genuine floor is a labelled cell
  (`engine_side`), a hole (`restrict_zoo`) or the other branch of its dichotomy (`hinge_side`).
  A stipulation can never shadow a proven cell.
* A swept tau matrix never contains the `none` state: a τ-bot always terminates.
* The unit of EGT work is the distinct matrix, not the grid point: runs are keyed by a hash of the
  cells, so grid points with the same cells share one run directory.
* Package management is `uv` only.

The design records are the notes under `../engine/PrisonersDilemma/Research/Notes/`
(`TAUBOTS.md`, `SPRIME_SOURCE_OF_TRUTH.md`, `EGT_FINDINGS_SPRIME.md`).

# Open-Source Game Theory, mechanized

A Lean 4 mechanization of **open-source game theory** (Critch 2022: agents that read each other's
source code and search for bounded proofs about it), the **partial-transparency** extension
(τ-bots: agents that receive a blurred signal about their opponent), and the **evolutionary**
analysis of the resulting populations. Companion to the paper *Partial Transparency in OSGT*.

## Layout

| Directory | What it is | Build / run |
|---|---|---|
| [`arith/`](arith/) | **The proof system of the paper: PA-`S'`** — Peano Arithmetic with a provability predicate bounded by proof length, on the [Foundation](https://github.com/FormalizedFormalLogic/Foundation) library. The bounded Löb theorem proved unconditionally, the outcome matrix re-proved cell by cell, the tau rows, the floor dichotomies. Start with [`arith/ArithS/Tour.lean`](arith/ArithS/Tour.lean) and [`arith/ArithS/README.md`](arith/ArithS/README.md). | `cd arith && lake build --try-cache` |
| [`engine/`](engine/) | **The host**: the agent language (`Prog`), the fuelled evaluator, the bot zoo, the τ-bot DSL, and the typed outcome-theorem template with its linter and census. Also the rule-based system `S` and its outcome theorems, which `arith/` imports (search-free cells transfer) and the Python layer loads as the comparison source. `arith/` depends on it; it never imports `arith/`. | `cd engine && lake build` |
| [`app/`](app/) | **The Python core** (`pd_runner`): the outcome matrices read from the two Lean exports (never from Lean source), the tau layer (signals, σ-families, the Def 3 ≡ Def 4 certification), and the EGT stages (ESS, invasion graphs, faces, Nash, replicator, Moran). The paper's experiments and the figure generators in `latex/scripts/` run on it. | `cd app && uv sync && uv run pytest` |
| [`pipeline/`](pipeline/) | **The LLM pipeline** (`pd_pipeline`): bots written from natural language, outcome proofs written by an agent and judged by the Lean kernel, the faithfulness reviewer, the web UI. Out of the paper's scope; depends on `app/`. | `cd pipeline && uv sync && uv run pd-serve` |
| [`latex/`](latex/) | The paper sources, the figure and table generators (`scripts/`), earlier notes and talks. | — |
| [`llm-distillation/`](llm-distillation/) | A separate experiment (fitting LLM play to the matrix); kept for later work. | — |

The two JSON exports are the only interface between Lean and Python:
`lake exe export_sprime_outcomes` (in `arith/`) writes `app/generated/sprime_outcome_theorems.json`
and `sprime_tau_rows.json`; `lake exe export_outcomes` (in `engine/`) writes `outcome_theorems.json`
and `tau_rows.json`. Everything the Python side computes is deterministic arithmetic on those files.

## Trust base

No project axioms: every theorem in `engine/` and `arith/` rests on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — `arith/ArithS/Audit/` runs `#print axioms` over the
whole build. No `sorry`. Every matrix cell is a theorem on a typed template, checked by a linter and a
census inside `lake build`, or an explicitly stated open case (a floor dichotomy).

Project conventions for contributors and agents are in [`CLAUDE.md`](CLAUDE.md); the design notes
live under [`engine/PrisonersDilemma/Research/Notes/`](engine/PrisonersDilemma/Research/Notes/).

## Toolchain

Lean `v4.33.1` (`lean-toolchain` in both Lean packages; mathlib pinned in `engine/`, Foundation
pinned in `arith/`), Python ≥ 3.11 managed with [`uv`](https://docs.astral.sh/uv/). CI builds both
Lean packages (`.github/workflows/lean_action_ci.yml`).

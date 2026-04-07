# Open Source Game Theory

This repository combines a Lean 4 formalization of Prisoner's Dilemma models with a small Python runner and the LaTeX sources for the surrounding thesis material.

## Repository Layout

- `engine/` - Lean 4 project with the formal model, bots, and proofs.
- `app/` - Python orchestration layer that generates Lean snippets, runs checks, and parses results.
- `latex/` - thesis and talk sources, plus generated build artifacts.

## What It Does

The Lean engine defines the game semantics and proofs. The Python app automates matchups between programs by generating Lean code, running `lake env lean`, and returning the resulting actions or outcome claims.

## Quick Start

### Lean engine

```bash
cd engine
lake build
```

### Python runner

```bash
cd app
uv sync
uv run run-matchup --left cooperateBot --right defectBot
```

## Notes

- The Lean project is self-contained inside `engine/`.
- Generated Lean files and logs from the Python runner live under `app/generated/`.
- The thesis and presentation sources are kept separate from the code in `latex/`.

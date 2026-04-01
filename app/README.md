# pd-runner

Python orchestration layer for the Lean project in `../code`.

## Goal

- Accept two program names (bots) from the user.
- Generate a Lean file that evaluates their chosen actions.
- Run Lean checks via `lake env lean`.
- Parse and return resulting actions.

## Quick Start (uv)

1. `cd app`
2. `uv sync`
3. `uv run run-matchup --left cooperateBot --right defectBot`

## Useful uv Commands

- Install dev tools (`pytest`, `ruff`):
	- `uv sync --extra dev`
- Install API stack (`fastapi`, `uvicorn`):
	- `uv sync --extra api`
- Run tests:
	- `uv run pytest`

## Notes

- This app assumes the Lean project lives at `../code`.
- Generated Lean snippets are written to `generated/lean/`.
- Build/eval logs can be stored in `generated/logs/`.

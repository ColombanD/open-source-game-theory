# pd-runner

Python orchestration layer for the Lean project in `../engine`.

## Goal

- Accept two program names (bots) from the user.
- Generate a Lean file that checks a discovered outcome theorem.
- Run Lean checks via `lake env lean`.
- Parse and return resulting actions.

## Quick Start (uv)

1. `cd app`
2. `uv sync`
3. `uv run run-matchup --left CooperateBot --right DefectBot`

### Cleaner output and file cleanup

- Print only actions:
	- `uv run run-matchup --left CooperateBot --right DefectBot --quiet`
- Delete generated Lean file after execution:
	- `uv run run-matchup --left CooperateBot --right DefectBot --no-keep-file`
- Combine both:
	- `uv run run-matchup --left CooperateBot --right DefectBot --quiet --no-keep-file`

### Optional Claim Check

- Check a claim against a discovered Lean outcome theorem:
	- `uv run run-matchup --left CooperateBot --right DefectBot --claim-left C --claim-right D`
- Try an intentionally false claim (should error):
	- `uv run run-matchup --left CooperateBot --right DefectBot --claim-left D --claim-right C`

## Useful uv Commands

- Install dev tools (`pytest`, `ruff`):
	- `uv sync --extra dev`
- Install API stack (`fastapi`, `uvicorn`):
	- `uv sync --extra api`
- Run tests:
	- `uv run pytest`

## Notes

- This app assumes the Lean project lives at `../engine`.
- Legacy names such as `cooperateBot`, `defectBot`, and `dBot` are still accepted and mapped to the new Lean bot names.
- Generated Lean snippets are written to `generated/lean/`.
- Build/eval logs can be stored in `generated/logs/`.

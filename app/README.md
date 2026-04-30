# pd-runner

Python orchestration layer for the Lean project in `../engine`.

## Goal

- Accept two program names (bots) from the user, including `Bot:k` parameterized bots.
- Generate a Lean file that checks a discovered outcome theorem.
- Run Lean checks via `lake env lean`.
- Parse and return resulting actions.

## Quick Start (uv)

1. `cd app`
2. `uv sync`
3. `uv run run-matchup --left CooperateBot --right DefectBot`

List bots discovered from the Lean engine:

- `uv run run-matchup --list-bots`

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

### Parameterized Bots

- Use `Bot:k` for a concrete natural-number parameter:
	- `uv run run-matchup --left CupodBot:3 --right CooperateBot`
- Reversed theorem lookup still works:
	- `uv run run-matchup --left CooperateBot --right CupodBot:3`
- Use `Bot:?` for existential parameter theorems:
	- `uv run run-matchup --left 'CupodBot:?' --right DefectBot`
- `Bot:?` first tries universal parameter theorems. If a theorem proves every `k`, the result is reported as `kind: all_parameters` with `witness: any`.
- If no universal theorem matches, `Bot:?` tries existential theorems and reports `kind: exists_parameter` with `witness: unknown`.
- Existential theorems do not certify concrete parameters. For example, `CupodBot:?` can use a theorem proving `∃ k`, but `CupodBot:3` requires a theorem about that concrete `k`.

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
- Parameterized names use colon syntax: `CupodBot:3`, `DupocBot:10`, or `CupodBot:?`. Quote `Bot:?` in shells like zsh so `?` is not treated as a glob.
- Unknown bot errors include the available bot list. You can also run `uv run run-matchup --list-bots`.
- Generated Lean snippets are written to `generated/lean/`.
- Build/eval logs can be stored in `generated/logs/`.

# pd-runner

Python orchestration layer for the Lean project in `../engine`.

## Goal

- Accept two program names (bots) from the user, including `Bot:k` parameterized bots.
- Generate a Lean file that checks a discovered outcome theorem.
- Run Lean checks via `lake env lean`.
- Parse and return resulting actions.
- **Phase 2:** Use an LLM agent to automatically write new Lean proofs for bot matchups.

## Quick Start (uv)

1. `cd app`
2. `uv sync`
3. `uv run run-matchup --left CooperateBot --right DefectBot`

List bots discovered from the Lean engine:

- `uv run run-matchup --list-bots`

### CLI Parameters

- `--left BOT`: left bot name, for example `CooperateBot` or `CupodBot:3`.
- `--right BOT`: right bot name, for example `DefectBot` or `CupodBot:?`.
- `--list-bots`: print the bots discovered from the Lean engine and exit.
- `--claim-left C|D` and `--claim-right C|D`: check a claimed action pair.
- `--quiet`: print only the action pair.
- `--no-keep-file`: delete the generated Lean file after execution.
- `--json`: print the result as JSON.

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

---

## Phase 2 — LLM Proof Agent

The `llm/`, `eval/`, and `services/proof_service.py` + `services/library_writer.py` modules implement an agentic proof-writing pipeline. Given a bot pair and claimed outcome, the agent automatically writes and verifies a Lean 4 proof.

### Architecture

```
ProofRequest (bot pair + outcome)
    │
    ├─ retrieval.py        — fetch relevant existing theorem files as few-shot context
    ├─ prompts.py          — build system prompt (embeds Program.lean + Dynamics.lean verbatim;
    │                        adds Axioms.lean for .search bots like CupodBot/DupocBot)
    │
    └─ proof_service.py    — agentic loop (AnthropicClient + ToolHandler)
            │
            ├─ run_lean_proof tool    — write candidate to temp file, run lake env lean, return errors
            └─ read_library_file tool — read any file under engine/PrisonersDilemma/ for reference
            │
            └─ ProofResult (verified Lean source + iteration count)
                    │
                    └─ library_writer.py — write to engine/PrisonersDilemma/Theorems/,
                                           run lake build, roll back on failure,
                                           optional human-acceptance gate
```

### Module reference

| Module | Purpose |
|---|---|
| `llm/client.py` | `AnthropicClient` — multi-turn tool-use loop with adaptive thinking and system-prompt caching. `ToolHandler` — registry mapping tool names to Python callables. |
| `llm/tools.py` | Claude tool schemas and implementations: `run_lean_proof` (fast per-iteration Lean check, no `lake build`) and `read_library_file` (read any file under `engine/PrisonersDilemma/`). |
| `llm/retrieval.py` | `retrieve_few_shots` — returns the most relevant existing theorem files for a bot pair (name match first, then content match). `list_known_outcome_theorems` — scans the discovered theorem registry for already-proven outcomes involving the bots. |
| `llm/prompts.py` | `build_system_prompt` — embeds the real `Program.lean` and `Dynamics.lean` source; adds `Axioms.lean` when either bot uses `.search` (CupodBot, DupocBot). `proof_request_message` — builds the per-request user message with the theorem stub, known theorems, and few-shot files. |
| `services/proof_service.py` | `search_proof(ProofRequest) -> ProofResult` — the agentic loop. Retrieves context, builds prompt, runs tool-use loop, extracts final `\`\`\`lean\`\`\`` block. Raises `ProofSearchError` on failure. |
| `services/library_writer.py` | `write_proof_to_library(ProofResult)` — writes a proven proof to `engine/PrisonersDilemma/Theorems/`, verifies with `lake build`, rolls back on failure. Never overwrites existing files. |
| `eval/harness.py` | Evaluation harness: re-proves 10 held-out theorems and reports pass rate, iteration count, and wall time. |

### Running the proof agent

Requires `ANTHROPIC_API_KEY` set in your environment (API credits separate from Claude Pro).

```bash
# Full eval run (calls LLM + Lean for all 10 cases)
uv run python -m pd_runner.eval.harness --model claude-sonnet-4-6 --output results.json

# Dry run — tests retrieval + prompt plumbing without any API calls
uv run python -m pd_runner.eval.harness --dry-run

# Options
#   --model MODEL         Anthropic model ID (default: claude-opus-4-7)
#   --max-iterations N    Max tool-use iterations per proof (default: 20)
#   --output FILE         Save results as JSON
#   --dry-run             Skip LLM and Lean, test plumbing only
```

### Eval case tiers

| Tier | Bots | Difficulty |
|---|---|---|
| 1 | CooperateBot, DefectBot | Trivial — `.const` action, `unfold` + `rfl` |
| 2 | MirrorBot, OBot, DBot | One-step simulation, `unfold` + `simp` |
| 3 | TitForTatBot, EBot | Multi-step, requires inspecting bot definitions |

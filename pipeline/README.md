# `pipeline/` — `pd_pipeline`, the LLM pipeline

An agentic layer over the Lean engine: it writes **bots from natural-language strategy
descriptions**, **proves their outcome theorems** with an LLM whose output is judged by the Lean
kernel, reviews the bots for faithfulness, and serves a web UI for the whole flow with human
acceptance gates. It is **out of the paper's scope** (the paper's Lean results were drafted with
it and judged by the kernel; nothing else of it is reported) and lives apart from the core so the
core stays a deterministic analysis library. It depends on [`../app/`](../app/) (`pd_runner`: the
matrices, the tau layer, EGT) and on [`../engine/`](../engine/) (the Lean library it writes into).

```
pipeline/
  src/pd_pipeline/
    services/   proof_service, proof_episodes, verdicts    — the proof agent (Proposer → Compiler → Reviewer → Memory)
                bot_service, bot_expectation, bot_profile,  — the bot writer and the faithfulness reviewer (tiers A1/A2/B)
                bot_judge, bot_rewriter
                library_writer, lemma_library,              — growth: new theorem files, derived rules, Tier-2 constructor
                constructor_proposals, constructor_integration   proposals and their integration agent
                matchup_service, sheets                     — one matchup by generated Lean; the Google-Sheet push
    llm/        client (Anthropic), openai_client, factory, prompts, retrieval, tools, library_search, lean_index
    lean/       executor, generator, parser, templates, interact (LeanInteract REPL)
    api/        FastAPI app + static UI (`pd-serve`)
    eval/       harness, run_bot_matrix, run_bot_pipeline, run_bot_writer, run_pipeline, outcome_prepass
    cli.py      `run-matchup`
    settings.py models, budgets, retry policy (re-exports the core's CELL_SOURCE / FLOOR_POLICY)
    config.py   paths: this project's generated/ and the engine directory
  generated/    constructor_proposals/, prepass/, lemma_attempts/ (tracked records); outcomes/, reviews/,
                integrations/, lean/, logs/ (per-run artefacts, gitignored)
  docs/BOT_REVIEWER.md   the reviewer's design note — read before touching bot_profile/bot_expectation/bot_judge
```

## Quick start

```bash
cd pipeline
uv sync --extra dev          # installs pd-runner from ../app (editable)
cp .env.example .env         # fill in ANTHROPIC_API_KEY (and MISTRAL_API_KEY for leanstral)
uv run pytest
uv run pd-serve --reload     # the web UI at http://127.0.0.1:8000
uv run run-matchup --left CooperateBot --right DefectBot
```

Do **not** `export ANTHROPIC_API_KEY` from your shell rc file: a global export is inherited by every
process on the machine. `pipeline/.env` is gitignored and loaded when `pd_pipeline` is imported; a real
environment variable still wins for one-off overrides.

Pinned: `anthropic < 1` — the 1.x SDK moved to `httpx2` and rejects the `httpx.Timeout` the calibrated
client passes; the agent baselines were measured on the 0.12x SDK.

## The proof agent

Given a bot pair, the agent writes a theorem on the strict template
`@[outcome] theorem llm_outcome_<L>_vs_<R> : OutcomeSpec <regime> <pad> L R (some (.X, .Y))` and
iterates against Lean (a persistent LeanInteract REPL, falling back to `lake env lean`). It finishes
through the `submit_verdict` tool — `proved | open_bistable | open_blocked | constructor_proposed` —
and a `proved` submission is re-compiled with the library's own linter (`#validate_outcome`) before
it counts. Because the statement is fully concrete, compilation is correctness, modulo the
natural-language → Lean translation of the *bot*, which the reviewer addresses:

* **Tier A1** — a blind expectation extractor predicts the bot's profile against four canonical
  opponents from the description alone (it never sees the generated Lean).
* **Tier A2** — a certified behavioral profile from the engine's computable evaluator.
  **Note:** this tier runs `PrisonersDilemma.Decidability.T31EngineDecider`, which was removed from
  the engine on 2026-10-29 (git history before `3f99464` has it); restore it before using Tier A2.
* **Tier B** — a judge agent on the residual only; advisory, never an acceptance criterion.

```bash
uv run python -m pd_pipeline.eval.harness --dry-run                      # plumbing only, no API calls
uv run python -m pd_pipeline.eval.harness --model claude-opus-4-7 --output results.json
uv run python -m pd_pipeline.eval.run_bot_pipeline --bot-a-name KindBot --bot-a-strategy "..." \
    --bot-b-name MeanBot --bot-b-strategy "..."
```

Every run persists to `generated/outcomes/<L>_vs_<R>_<stamp>/` (per-episode meta, transcript, the
final Lean source). The growth tools (`add_base_lemma`, `propose_pf_constructor`) are registered only
outside the eval harness; accepted constructor proposals are integrated by an agent in a git worktree
and land only after a human reviews the diff.

## Outcome matrix → Google Sheet

`uv run python -m pd_runner.eval.outcome_matrix --push` pushes the matrix through
`pd_pipeline.services.sheets` (service-account JSON at `pipeline/.secrets/sheets-service-account.json`
or `PD_SHEETS_CREDENTIALS`; worksheet `PD_SHEETS_WORKSHEET`, spreadsheet `PD_SHEETS_SPREADSHEET_ID`).
The worksheet is rewritten on every push; curate `Open Problem` / `Tried` in `app/outcome_status.toml`.

## `run-matchup`

Checks one matchup by generating a Lean file that cites a discovered outcome theorem and running
`lake env lean` on it: `--left BOT --right BOT`, `Bot:k` for a concrete budget, `Bot:?` for a
universal/existential theorem, `--claim-left C|D --claim-right C|D` to check a claim, `--list-bots`,
`--json`, `--quiet`, `--no-keep-file`. Generated files go to `generated/lean/`.

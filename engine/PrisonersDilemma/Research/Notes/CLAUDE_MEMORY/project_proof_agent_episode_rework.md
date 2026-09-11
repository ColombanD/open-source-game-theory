---
name: proof-agent-episode-rework
description: "2026-07-30 AxProverBase-style rework of the proof agent — episode loop, notebook memory, submit_verdict tool, deterministic exit verification, 4-breakpoint caching; re-baselining plan and gotchas"
metadata: 
  node_type: memory
  type: project
  originSessionId: 617e1fd5-ce02-462e-b136-ef0c640621c9
  modified: 2026-07-31T13:26:56.161Z
---

**2026-07-30: the proof agent was fully reworked** (AxProverBase, arXiv 2602.24273: Proposer→Compiler→Reviewer→Memory). Full architecture description now lives in CLAUDE.md ("Proof-agent architecture"); this note holds what CLAUDE.md doesn't.

Key non-obvious facts:
- **Reviewer is deterministic, NOT an LLM** — Colomban's strict `outcome_X_vs_Y` template makes cheat-checking decidable (re-compile + statement parse in `services/verdicts.py::check_proved_source`). Chosen deliberately over AxProverBase's LLM reviewer.
- **User decisions (fixed)**: sorry-sketch goal-state extraction DEFERRED to v2 (seam = `CompileService`/`CompileReport.goals` in proof_episodes.py — always None in v1); the `#eval` prepass oracle stays OUT of the agent (outcome discovery is part of what the thesis evaluates); notebook trigger is HYBRID (voluntary tool + forced reflection turn at episode end if not updated within last 2 turns; never-updated always triggers).
- **Re-baselining plan**: numbers from before the rework are non-comparable. Baseline A = `--max-episodes 1` (structured verdicts only), B = default 3 episodes, C = after any model-default change. This is a free architecture ablation for the paper's E3. Model default stays `claude-opus-4-7` everywhere (settings.DEFAULT_MODEL) — change it only at a baseline point.
- **Live smoke verified** (case 0): turn-2 cache_read = 91,944 tokens (full prompt cached); system block A byte-identical across all matchups (asserted in a test) so it caches across a whole matrix run.
- **Gotcha**: `submit_verdict(constructor_proposed)` cross-checks the proposal name against proposals recorded THIS session OR bundle dirs on disk (`_proposal_exists`); `propose` sanitizes names (alnum+underscore), both raw and safe forms accepted.
- **Legacy JSONL compat**: run_bot_matrix `--resume` reads both old (`bot_a`/`bot_b`) and new (`left_bot`/`right_bot`) record keys.
- The bot-writer agent (`bot_service.py`) still uses the OLD prose protocol (```lean fence extraction) — only the proof agent was reworked.

**2026-07-31 additions** (commit c59118a; integration agent ported in 66556d1):
- **`search_library` tool** (llm/library_search.py) — closed-world LeanSearch replacement; web search was rejected DELIBERATELY (nothing about PD.* exists online + public-repo leak channel past the eval filter). Don't re-propose web search.
- **LeanInteract fast checking** (lean/interact.py) — measured on the 16GB dev Mac: cached-env checks ~0.03s vs ~0.7s warm `lake env lean` (~20x); env creation ~2s per import block. TRAPS: AutoLeanServer's default 0.8 memory guard trips chronically on macOS (near-full by design) → we run 0.95 + session-cached envs + two-strikes auto-disable; `LocalProject(directory=...)` is keyword-only. `PD_LEAN_INTERACT=0` disables. Verdict gate + library_writer ALWAYS file-compile.
- **Sketch-then-fill is LIVE** (not v2 anymore): run_lean_proof reports goals at sorries; sketches never displace best_attempt; verdict gate rejects sorry.
- First wild multi-episode save observed 2026-07-31: OptimBot_vs_CooperateBot ep1 turn_cap → notebook → ep2 proved.
- **Open-verdict one-shot retry (2026-07-31, same day as the OptimBot_vs_DefectBot ep1 open_blocked run that motivated it)**: episodes were pure crash-recovery (any submit_verdict — incl. open_* — ended the run at the `verdict_input` check). Now the FIRST open verdict buys ONE fresh retry episode (prior verdict+explanation injected into `_episode_block`, "re-derive the blocker from scratch"); the second open verdict (or one on the last episode) is final; retry-with-no-verdict falls back to the retried open verdict instead of `exhausted`. `ProofState.prior_open_verdict` is both the carrier and the retry-spent flag. Unit-tested in test_proof_pipeline.py (fake AnthropicClient, scripted EpisodeResults). CAVEAT for re-baselining: open verdicts now cost up to 2 episodes of tokens — baseline-B numbers before/after this change are not comparable on open matchups (JustBot-vs-MirrorBot eval case now runs 2 episodes before passing).
- Related: [[project_outcome_prepass_guardfastn]], [[project_stale_import_cleanup]], [[project_onedrive_lake_replay_timeout]]

---
name: project-outcome-matrix-sheet-sync
description: "Google Sheet outcome-matrix sync — acceptance rules, status file, gspread push, app trigger (2026-07-30)"
metadata: 
  node_type: memory
  type: project
  originSessionId: df85cd50-954f-4c8c-a44f-b112fdf999ef
  modified: 2026-07-30T11:43:37.252Z
---

The tracking Google Sheet matrix is now generated+pushed programmatically (2026-07-30):

- **Extractor** `app/src/pd_runner/eval/outcome_matrix.py` — Colomban's acceptance rules:
  bots = `Theorems/` directory names ONLY, empty placeholder dirs count, sole exclusion
  `LlmGenerations` (no PrudentBot2/JustBot2; OptimBot added as empty dir 2026-07-30); theorem
  names must be exactly `(llm_)?outcome_<A>_vs_<B>` (NO `_floor`/`_floor2`/`_defended`/
  `_k<N>` suffixes — floor-regime results never fill a cell); all quantifier shapes
  accepted incl. `∃k,∀fuel`; side-hypothesis proofs (binders named `h…`) get a `†` flag;
  `= none` renders `None`.
- **Negative knowledge** lives in `app/outcome_status.toml` (`[[open]]`/`[[tried]]`/
  `[[rework]]`, unordered pairs; precedence open > rework > tried) — the Lean tree has
  NO open-problem markers. Floor-only LegibleBot/WaryBot pairs = `rework` ("Need rework",
  blue); genuinely open (CupodBot×DupocBot, JustBot×MirrorBot + 4 more Cupod/Dupoc-family
  per Colomban) = `open` (red); `tried` = yellow; `None` = green. Proven theorem beats a
  stale status entry (warning). Unlisted+unproven = empty cell.
- **Failure-path wiring (2026-07-30)**: pipeline proof failures auto-append `[[tried]]`
  (kinds no_output/error; `append_status` never downgrades); OUTCOME OPEN verdicts
  (kinds open_*) set `job.open_suggestion` → UI button → human-gated `POST /matrix/status`
  appends `[[open]]`. Sheet re-syncs best-effort after both.
- **Push** `app/src/pd_runner/services/sheets.py` (gspread, service account at
  `app/.secrets/sheets-service-account.json` or `PD_SHEETS_CREDENTIALS`); writes ONLY
  the `Auto Matrix` worksheet (clear+rewrite), never hand-edited tabs. Triggers:
  CLI `--push`, `POST /matrix/sync` + UI button, and best-effort auto-sync after each
  accepted proof in `pipeline_task.py`.
- Setup doc: `app/README.md` "Outcome matrix → Google Sheet". Sheet ID default in
  sheets.py; URL in `engine/README.md`.
- Known pre-existing test failures (unrelated): 2 in `tests/test_proof_pipeline.py`
  (`build_system_prompt` fixture missing `Base/Helpers.lean`).

Related: [[project-outcome-prepass-guardfastn]], [[project-stale-import-cleanup]]

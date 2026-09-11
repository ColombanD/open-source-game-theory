---
name: stale-import-cleanup
description: 2026-07-27 removed ~1083 stale engine imports; method + root cause (few-shot import-block copying)
metadata: 
  node_type: memory
  type: project
  originSessionId: fd104ecd-ee1f-4a4d-b244-5347de882dfc
  modified: 2026-07-27T15:50:24.321Z
---

2026-07-27: swept the Lean engine for stale imports — 1,087 import lines removed across 89 files (net −1,083 after 4 direct-import fixes), build green on both targets. Method (Lean has no unused-import lint): textual heuristic (bot / `A_vs_B` / cross-bot `Helpers` key absent from file body) → per-file `lake env lean` with candidates stripped (~2.6 s/file, parallelized) → apply → full `lake build` → re-add direct imports where a file had silently relied on transitive supply (3 files: CIMCIC/vs_DefectBot, PrudentBot/vs_DupocBot, PrudentBot/vs_MirrorBot). Research/Spikes candidates were all false positives (lemma names don't embed bot names) — compile check correctly kept them.

**Why:** the bloat re-accumulates — proof-agent-generated theorem files copy whole import blocks from few-shot examples (JustBot files carried ~26 stale imports each, entire CupodTrollBot/DupocBot suites).

**How to apply:** to stop recurrence, trim the import block the app's proof agent emits (few-shot prompts / [[llm-bot-outcomes-status]] pipeline) or re-run this sweep after batches of generated theorems land. Compile-pass ≠ unused when another import transitively supplies the module — final full `lake build` is the real gate.

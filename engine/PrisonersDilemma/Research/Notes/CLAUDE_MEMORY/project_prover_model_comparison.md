---
name: project-prover-model-comparison
description: E4 model-comparison note exists; leanstral vs Claude case study on DIMCID-vs-CupodBot and the harness fixes it motivates
metadata: 
  node_type: memory
  type: project
  originSessionId: b5c2ad01-6b70-47e5-b38f-d2835ec87f47
  modified: 2026-08-05T13:25:55.169Z
---

`engine/PrisonersDilemma/Research/Notes/PROVER_MODEL_COMPARISON.md` accumulates E4
(prover-baseline) case studies. Case 1 (2026-08-05): leanstral-1-5 vs claude-opus-4-8
on DIMCID-vs-CupodBot, same harness. Claude: `open_blocked` (C,C) in 16 min/$3.97 with
the full wall analysis (guard-box subscript wall; WV can't force D-atoms false — dual of
WaryBot). Leanstral: 6 h, 3/34 green compiles, correct (C,C) intuition, NO verdict in 62
turns; its notebook was truncated mid-key-sentence by the 4000-char cap.

**Why:** the E4 paper claim is that the domain gap is metatheoretic judgment + verdict
discipline, not Lean syntax. n=1 and wall-shaped by selection — balance with provable cells.

**How to apply:** pending harness fixes motivated by case 1 (not yet implemented):
(1) escalate ignored submit_verdict reminders to a verdict-only final turn in
`llm/openai_client.py`; (2) bounce over-cap notebook writes instead of silent truncation;
(3) audit the forced end-of-episode notebook reflection on the OpenAI-compat path (ep3
never reflected). DIMCID-vs-CupodBot is still NOT in `outcome_status.toml` despite two
open_blocked verdicts (human gate never clicked). Related: [[project-proof-agent-episode-rework]].

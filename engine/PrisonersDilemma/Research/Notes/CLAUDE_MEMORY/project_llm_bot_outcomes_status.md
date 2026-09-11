---
name: project-llm-bot-outcomes-status
description: "Status of outcome proofs for the four LlmGenerations bots (JustBot, PrudentBot, CIMCIC, DIMCID)"
metadata: 
  node_type: memory
  type: project
  originSessionId: 0e89e4c0-be94-4940-9395-a8d71d212f23
---

Outcome proofs for the four `Bots/LlmGenerations/` bots, written 2026-06-12 in
`Theorems/LlmGenerations/` (template = DupocBot theorem file). Full `lake build` green.

- **JustBot**: vs CooperateBot (C,C) ✓, vs DefectBot (D,D) ✓. Mirror/TFT deferred
  (need Löb-style reasoning via the *mutated* DupocBot — see bug below).
- **PrudentBot**: vs CooperateBot (D,C) ✓, vs DefectBot (D,D) ✓. Clean (`.bot`-barriered
  `.sim` probe, DBot/OBot machinery). **vs MirrorBot = (D,D) ✓** (agent-proved,
  `outcome_PrudentBot_vs_MirrorBot.lean`). NOT (C,C): the cooperation atom is
  semantically FALSE and provably unprovable; PrudentBot's prudence `.ite` blocks the
  Löb fixed point that DupocBot reaches. See [[project-itebranchsearch-rule]] for the
  full "why it's forced, not an engine artifact" argument (the curried-guard /
  Type-Prop-firewall reasoning + `prudent_mirror_loeb_premise_implies_false`).
- **CIMCIC**: vs CooperateBot (C,C) ✓. vs DefectBot = incompleteness boundary (unproved).
- **DIMCID**: vs DefectBot (D,D) ✓. vs CooperateBot = incompleteness boundary (unproved).

CIMCIC/DIMCID required the [[project-weakenimpl-rule]] engine extension.

**JustBot source bug — FIXED 2026-06-12.** Its guard originally referenced
`DupocBot k` WITHOUT a `.bot` wrapper, so `subst` descended and mutated DupocBot's
internal placeholders. Now `.bot (DupocBot k)` (the `.bot` scope barrier freezes it).
Coop/Defect proofs unchanged in outcome, retargeted at `.bot (DupocBot k)`.
Note: `.bot` is needed for ANY literal bot reference in source, not just inside
`.sim` (the existing library only happens to use it under `.sim`); the rule comes
from `Prog.subst` descending into `.search` guards too. Mirror/TFT for JustBot still
deferred: opponent-side is now `.bot (DupocBot k)`, which differs from the DupocBot
theorem file's plain-`DupocBot k` opponent, so those lemmas don't transfer directly.

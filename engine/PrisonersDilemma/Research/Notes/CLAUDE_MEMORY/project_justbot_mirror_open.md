---
name: project-justbot-mirror-open
description: "JustBot vs MirrorBot is PROVEN (C,C) at large k by bounded Löb — the old 'genuinely bistable/open' analysis was WRONG; never cite it as open"
metadata:
  type: project
---

`llm_outcome_JustBot_vs_MirrorBot : ∃k₂, ∀k>k₂, ∃fuel, outcome fuel (JustBot k) MirrorBot = some (C, C)`
(`Theorems/JustBot/vs_MirrorBot.lean`, commit 64c4a2e). Route: `jm_loeb_premise` derives
`□_k φ_B → φ_B` for φ_B = "MirrorBot plays C vs `.bot (DupocBot k)`" (`Pf.botSearchStep` reads the frozen
Dupoc's guard, `Pf.simStep` reads MirrorBot, glued by `implTrans`), then `pblt_engine_id` makes φ_B
provable past a threshold, soundness gives the play, and JustBot's guard fires.

**Why:** the 2026-06-15 analysis in this note's previous version claimed the cell was a bistable fixpoint
with a SEMANTIC obstruction ("not the missing botSearchBranch rule"). That was backwards: φ_B is a
self-fulfilling Löb fixpoint (φ_B ⟺ □φ_B), which is exactly what bounded Löb resolves in favour of
provability once `S` can read the frozen searcher — `botSearchStep` (added the same day) was the
missing rule. Caught 2026-08-25 when the stale claim was repeated to Colomban and he pushed back.

**How to apply:** a "bistable, no sound rule can exist" verdict is only warranted when the Löb premise
`□φ → φ` is NOT derivable for ANY formula the guard reduces to — check the frozen-bot reformulation
(φ_B) before the real-matchup formula (φ). Frozen `.bot` guards are not a Löb dead end. See
[[project_botsearchstep_rule]], [[project_search_bot_threshold_prompt]].

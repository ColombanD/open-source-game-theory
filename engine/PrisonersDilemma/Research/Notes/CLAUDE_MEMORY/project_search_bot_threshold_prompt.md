---
name: project-search-bot-threshold-prompt
description: Proof agent prompt steers .search-bot matchups to large-k threshold theorems instead of OUTCOME OPEN
metadata: 
  node_type: memory
  type: project
  originSessionId: 2887bb11-922d-4bf6-ba1b-e865c5e14a6b
---

`app/src/pd_runner/llm/prompts.py` — for matchups where either bot uses `.search`
(i.e. takes a budget param `k`), `proof_request_message` now renders a **large-`k`
threshold template** instead of the bare unquantified `outcome (n+fuel) BotA BotB`
template:

```lean
theorem llm_outcome_A_vs_B :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (A k) (B k) = some (.X, .Y) := by
```

**Why:** the bare template left `k` free, so the agent (correctly) declared
`OUTCOME OPEN` — the outcome flips with `k` (small `k` → defect, large `k` →
Löb/Critch cooperation). A threshold theorem binding `k` IS provable and is the
expected answer (same shape as `DupocBot_vs_DupocBot`, DupocBot.lean:438).

**How to apply:** detection uses the existing `_bot_uses_search(bot)` helper.
System-prompt rules reframed so OUTCOME OPEN is reserved for genuinely undetermined
matchups (two incompatible fixed points, neither forced for large `k`), not "varies
with `k`". The per-request hint names `DupocBot_vs_DupocBot` as the template EXCEPT
when DupocBot self-play is itself the target (leak guard for the eval harness's
`exclude_bots`). Retrieval already surfaces `DupocBot.lean` (filename score 2) for
any DupocBot matchup, so the PBLT few-shot is available. See [[project-llm-bot-outcomes-status]].

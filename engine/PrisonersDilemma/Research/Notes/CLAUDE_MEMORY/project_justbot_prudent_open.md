---
name: project_justbot_prudent_open
description: "JustBot vs PrudentBot is OPEN — .bot(DupocBot) guard blocks the searchBranch leg; needs a botSearchStep rule to force (C,C)"
metadata: 
  node_type: memory
  type: project
  originSessionId: e27a9c3c-0197-4189-b83a-e3f6560beb6b
---

JustBot vs PrudentBot is genuinely OPEN under the current proof system S (verified the agent's 2026-06-15 OPEN verdict against the source — it is correct).

JustBot's guard is `.search k (.plays .opp (.bot (DupocBot k)) C) ...`. Against PrudentBot it substitutes to `proofSearch k (.plays (PrudentBot k) (.bot (DupocBot k)) C)` — i.e. "does PrudentBot cooperate vs the **`.bot`-wrapped** DupocBot?". This is the PrudentBot↔DupocBot modal cooperation loop, but DupocBot now appears as a `.bot`-wrapped *player* (PrudentBot's opponent).

The library closes the BARE loop in `loeb_premise_provable` (Theorems/LlmGenerations/PrudentBot.lean ~L1043) with two legs: `searchThenSearch_t` (PrudentBot's stacked search) + `Derivation.searchBranch` reading DupocBot's **bare** `.search` body, bridged by `atom_box_provable_impl`. Here leg2 would need to read a `.bot (.search …)` body — and S has transparency rules only for bare `.search` (`searchBranch`) and `.bot (.sim …)` (`botSimStep`); there is **no `.bot (.search …)` rule** (grepped the whole engine). So the cooperative Löb premise can't be assembled → (C,C) not provable; the defective fixed point is equally consistent → (D,D) not provable by refutation either.

Same `.bot`-freezes-self-reference structure as [[project_justbot_mirror_open]]. Caveat: the agent's "no rule forces either outcome for any k" is an absence-of-proof argument, not a Lean-checked impossibility (same status as the Mirror case).

**Unblocking path:** add a `botSearchStep` rule (the `.bot (.search …)` twin of `botSimStep` in Derivation.lean ~L77) — analogous to how [[project_itebranchsearch_rule]] unblocked Mirror/TFT. `botSimStep`'s soundness note argues `.bot`-as-own-body is sound because `subst` keeps the same `me` throughout; same argument should carry. This is an engine extension — the proof agent can't do it (ADD-files-only v1 rule). Until then, leave OPEN; don't re-investigate via the agent.

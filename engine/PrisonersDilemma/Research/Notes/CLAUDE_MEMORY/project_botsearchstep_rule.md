---
name: project_botsearchstep_rule
description: botSearchStep Derivation rule — S reads a .bot-wrapped .search body; the .bot(.search) twin of searchBranch/botSimStep
metadata: 
  node_type: memory
  type: project
  originSessionId: e27a9c3c-0197-4189-b83a-e3f6560beb6b
---

Added `Derivation.botSearchStep` (engine/PrisonersDilemma/Derivation.lean, right after `botSimStep`) on 2026-06-15. It is the `.bot (.search …)` twin of `searchBranch` (mirrors how `botSimStep` twins `simStep`).

Signature: `me = .bot (.search k ψ (.const a) (.const b))` ⟹ `Derivation (.impl (.box k (ψ.subst me opponent)) (.plays me opponent a))` — same Löb/PBLT conclusion shape as `searchBranch`.

Soundness case added to `Derivation.sound` (BaseTheorems.lean, after the `botSimStep` case): witness fuel `3` (one `.bot` unwrap via `eval`'s `.bot p => eval n me opponent p`, then `.search` guard step, then `.const a`); proof is `searchBranch`'s case + one extra unwrap. Sound for the same reason as `botSimStep`: `.bot` is read as `me`'s OWN body so `subst` keeps the same `me` throughout — no bare sub-program `.self`/`.opp` rebinding (the unsound general `.bot` transparency is `plays z → plays (.bot z)`).

Recursor impact: only `Derivation.sound` matches all constructors (needs the new case). `Derivation.size` uses a wildcard. `PlaysProof.rec` is a different type. Full `lake build` green after adding.

Motivation: unblocks the `.bot (DupocBot k)` leg in JustBot's guard — see [[project_justbot_prudent_open]]. NOTE: adding the rule alone does NOT auto-prove JustBot×PrudentBot; someone still has to write the outcome theorem assembling the cooperative Löb premise via this rule (the proof agent can't — ADD-files-only, and this was an engine change made by hand).

Build gotcha hit while verifying: a stale lowercase `Theorems.CupodTrollbot` .olean in `.lake/build` collided with `Theorems.CupodTrollBot` on the case-insensitive macOS FS ("environment already contains …"). No source imports the lowercase casing anymore; fix was `find .lake/build -iname '*cupodtroll*' -delete` then rebuild. Unrelated to botSearchStep.

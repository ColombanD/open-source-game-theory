---
name: project_searchthensearch_rule
description: "searchThenSearch_t + implTrans Provable rules unblock canonical PrudentBot (C,C) vs MirrorBot"
metadata: 
  node_type: memory
  type: project
  originSessionId: ecd79df8-6191-4ab3-88a9-e9d495a48861
---

The canonical (Critch) PrudentBot is `.search k₁ ψ₁ (.search k₂ ψ₂ (.const C)(.const D)) q` — cooperation `.search` at the root, prudence `.search` nested in its THEN branch ("prove opp cooperates AND prove opp defects vs DefectBot"). Bot def: `engine/PrisonersDilemma/Bots/LlmGenerations/PrudentBot.lean`.

**The wall it hit:** S's transparency rules only read a `.search` with `.const` branches (`searchBranch`) or a `.search` under an `.ite` (`iteBranchSearch_t`). Neither matches a `.search` nested in a `.search`, so PrudentBot's Löb cooperation premise was unbuildable → it defected (D,D) vs MirrorBot, same as the old `.ite`-wrapped version.

**Fix (two new Provable-level constructors in `Derivation.lean`, soundness proved in `BaseTheorems.lean`):**
- `Provable.searchThenSearch_t` — reads stacked `.search`/`.search`; CARRIES the inner (prudence) proof as a `Provable k₂ ψ₂'` premise (not Derivation: `□(atom)` has no Derivation, same Type/Prop split that motivates `weakenImpl`), CONCLUDES single-box `□_{k₁} ψ₁' → me plays c0`. PBLT-ready.
- `Provable.implTrans` — hyp-syllogism at Provable level (`φ→ψ`, `ψ→χ` ⟹ `φ→χ`); needed because `searchThenSearch_t` gives a Provable-only implication that can't chain with `simStep` via Derivation `hypSyll`.

Both need a minor-premise case in ALL THREE `Provable.rec` sites in BaseTheorems: `playsProof_sound` (trivial), `Provable_sound` (real), `proofSearch_monotone` (relax size bound). Forget one → "alternative not provided".

**Result:** `outcome_PrudentBot_vs_MirrorBot.lean` proves (C,C) end-to-end via PBLT (φ k = MirrorBot plays C vs PrudentBot k), no sorry/axiom. Löb premise leg sizes are `5·log2 k + 39`, fit by `linear_log2_add_le 6 60`. In index `LlmGenerations.lean`; full `lake build` green (3140 jobs).

**Two `.bot` rules — one UNSOUND, one SOUND. The distinction is which position `.bot` is read in.**
- UNSOUND (rejected): general `plays z o a → plays (.bot z) o a` — false when z has `.self`, because making `.bot z` the *player* rebinds "myself" to the box (scope barrier, `Program.lean:63-73`). MirrorBot=`.sim .opp .self` diverges: bare→opp-vs-MirrorBot, boxed→opp-vs-(.bot MirrorBot).
- SOUND (added): `Derivation.botSimStep` reads `me = .bot (.sim p q)` — `.bot` is `me`'s OWN body, so `subst` uses the same `me=.bot(.sim p q)` throughout, no rebinding. Soundness witness fuel n+2 (one `.bot` unwrap + one `.sim` step). Twin of `simStep`.

**`.bot MirrorBot` axiom DISCHARGED.** Was `axiom PrudentBot_plays_C_vs_bot_MirrorBot` (∀k form — too strong, false for small k). Now a theorem in the threshold form `∃k₂,∀k>k₂, play 4 (PrudentBot k) (.bot MirrorBot) = some C`, via its OWN searchThenSearch_t Löb premise about `.bot MirrorBot` (distinct fixed point from bare) + botSimStep for the mirror leg + PBLT. `EBot_plays_C_vs_PrudentBot` now takes the `.bot MirrorBot` coop play witness as a hyp; `outcome_PrudentBot_vs_EBot` folds the threshold into k₂. PrudentBot.lean (theorems) imports outcome_PrudentBot_vs_MirrorBot.lean (no cycle: outcome imports only the BOT def). No axiom, no sorry, 3140 jobs green.

Related: [[project_itebranchsearch_rule]] [[project_weakenimpl_rule]] [[project_search_bot_threshold_prompt]].

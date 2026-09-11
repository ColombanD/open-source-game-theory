---
name: project-itebranchsearch-rule
description: iteBranchSearch_t Derivation rule lets S read .search nested under an .ite (PrudentBot shape); does NOT force cooperation — PrudentBot vs MirrorBot is provably (D,D), not (C,C)
metadata:
  node_type: memory
  type: project
  originSessionId: app-fix
---

Added 2026-06-12. A new `Derivation` constructor `iteBranchSearch_t` in
`engine/PrisonersDilemma/Derivation.lean`, with its soundness case in
`Derivation.sound` (`BaseTheorems.lean`). Full `lake build` green, no new axiom,
no `sorry`.

**Shape:** `me = .ite (.sim .opp (.bot z)) a' (.search k ψ (.const c0) (.const c1)) q`.
Concludes (curried): `(.plays opponent (.bot z) a') → (□_k (ψ.subst me opp) → .plays me opp c0)`.
I.e. guard-fires → (Löb box premise → me plays c0). `modusPonens` discharges the
guard atom; the residual `□_k ψ' → me plays c0` is the PBLT-shaped hypothesis that
bare `searchBranch` gives for a *root* `.search` — now available when the `.search`
sits under an `.ite`.

**Why it had to be fused (not a generic iteBranch):** `eval`'s `.ite` rule runs BOTH
guard and selected branch in the OUTER frame (`eval n me opp ·`). A generic "branch
plays a" premise as a `.plays (p.subst me opp) opp a` atom is UNSOUND: the in-frame
search consults `proofSearch k (ψ.subst me opp)` whereas the search-as-its-own-program
consults the doubly-substituted `(ψ.subst me opp).subst (p.subst me opp) opp` — they
differ. Keeping `.search` explicit lets soundness reflect the outer-frame guard
directly via `proofSearch_spec`. Guard restricted to `.sim .opp (.bot z)` because that
probe's value is frame-independent (= `opponent` vs `.bot z`, the
`eval_sim_opp_bot_of_play` reduction, inlined since that helper is downstream of
BaseTheorems). Every real `.ite` bot uses this probe-guard idiom.

**Soundness proof notes (BaseTheorems.lean iteBranchSearch_t case):** witness fuel
`m+3` where `nb = m+1` (derive `nb≥1` from `hb`, else fuel-0 play = none ≠ some a').
`.ite` step → m+2 (guard `.sim` node), `.sim` step → m+1 (matches `hguard`), then-branch
`.search` + its `.const c0` run at m+1≥1. Drove it with explicit `rw [eval]` +
`show … = … from rfl` for the `.sim` reduction (NOT bare `simp [eval]`, which over-
unfolds `opponent` before `hguard` can fire), `(a'==a')=true` via `cases a' <;> rfl`.

**Recursor impact:** NONE on `Provable_sound`/`playsProof_sound` — `Derivation` is a
separate `Type`, not in the `Provable`/`PlaysProof` mutual block (contrast
[[project-weakenimpl-rule]] which DID need recursor surgery). `Derivation.size` is a
catch-all (`| φ, _ => φ.size`) so it stays total automatically. Only `Derivation.sound`'s
`induction` needed the new alternative.

**CRITICAL CORRECTION (was wrong before): `iteBranchSearch_t` does NOT make
PrudentBot vs MirrorBot cooperate. That matchup is (D,D), and (C,C) is IMPOSSIBLE
— proved, not deferred.** The rule is still sound/useful, but the "expected (C,C),
un-blocked" claim was false. Why:
- `iteBranchSearch_t` only yields the CURRIED `(guard atom) → (□_k φ → φ)`, because
  PrudentBot's root is `.ite` not `.search`. To get the closed `□_k φ → φ` that PBLT
  needs, you must discharge the guard atom `MirrorBot plays D vs DefectBot` via
  `modusPonens`. That atom is TRUE and `Provable` (Σ₁ `PlaysProof`/`atom` route) but
  has NO `Derivation` (`no_deriv_plays`: no Derivation concludes a bare `.plays`
  atom). `modusPonens` lives on `Derivation`, so the prefix cannot be stripped. The
  Löb premise stays curried and unusable.
- This is FORCED BY CONSISTENCY, not an engine gap. φ = `.plays MirrorBot (PrudentBot
  k) .C` is semantically FALSE (`mirror_never_C_vs_PrudentBot`: Mirror never plays C
  vs Prudent, at any fuel — propext only). If the closed Löb premise were derivable,
  PBLT → `Provable φ` → (soundness) `φ.interp` → `False`
  (`prudent_mirror_loeb_premise_implies_false`, in the proof file, uses only PBLT).
  Verified: adding a unified `Provable`-level modus ponens (interp-sound in isolation)
  makes the WHOLE system inconsistent. So the `Derivation`/`Provable` (Type/Prop)
  split is load-bearing for consistency — it's the firewall keeping source-transparency
  derivations from freely composing with arbitrary Σ₁ facts and then Löb-ing a false φ.
- Contrast DupocBot (root IS `.search`): clean uncurried `□_k φ → φ` for a TRUE φ
  (`Mirror plays C vs Dupoc`), so its Löb premise is real and (C,C) holds.

The agent proved `llm_outcome_PrudentBot_vs_MirrorBot = (D,D)` end-to-end
(`outcome_PrudentBot_vs_MirrorBot.lean`), correctly extending `no_deriv_plays` with the
`iteBranchSearch_t` case. It depends only on propext/Classical/Quot.

**Where `iteBranchSearch_t` IS still useful:** matchups where the `.ite`+`.search` bot
faces an opponent for which the guard fires AND the cooperation/defection atom is
genuinely TRUE (so the Löb premise is sound to build). JustBot Mirror/TFT may or may
not be (C,C) — must check φ's truth first, do NOT assume. See
[[project-llm-bot-outcomes-status]] and
[[project-search-bot-threshold-prompt]].

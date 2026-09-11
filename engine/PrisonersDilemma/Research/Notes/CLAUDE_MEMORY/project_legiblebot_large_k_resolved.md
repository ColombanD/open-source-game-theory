---
name: project-legiblebot-large-k-resolved
description: "LegibleBot large-k RESOLVED (2026-07-30) — all 11 matchups proven at staggered dials (2k+64, k); the \".box prover\" was derivable"
metadata: 
  node_type: memory
  type: project
  originSessionId: df85cd50-954f-4c8c-a44f-b112fdf999ef
  modified: 2026-07-30T12:30:18.198Z
---

**LegibleBot's "needs a .box prover" OPEN regime fell 2026-07-30** — no new engine
machinery needed. All 11 `outcome_LegibleBot_vs_*` large-k theorems landed in
`Theorems/LegibleBot/` (∃k₂ threshold form, staggered `LegibleBot (2*k+64) k`),
core in `Theorems/LegibleBot/Helpers.lean`:

- **The chain**: `Pf.searchBranch` (□_{2k+64}(□_k ψ) → ψ) + `Pf.box4 k (2k+64)`
  (□_k ψ → □_{2k+64} □_k ψ; the stagger pays box4's `a + |□_a φ| ≤ b` gate) +
  `implTrans` ⇒ single-box Löb premise `□_k ψ → ψ` ⇒ raw `pblt_engine` (f=id;
  NOT `pblt_engine_id` — pm k = 20·log2 k + 6·|X| + 200 exceeds its cap) ⇒
  `Pf m ψ` ⇒ `Pf_sound` for the play. LegibleBot cooperates with EVERYONE at
  large staggered k (guard is opponent-independent).
- Key helpers: `legible_loeb_premise` (hk: 3·log2 k + |X| + 40 ≤ k),
  `LegibleBot_cooperates_Pf` (opponent as k-indexed FAMILY X : Nat → Prog,
  |X k| ≤ B + 20·log2 k — needed for self-play), `LegibleBot_playC_gives_box`
  (recovers BOUNDED `Pf (2k+64) (□_k ψ)` from the C-play via interp; feeds
  CIMCIC's cross at citation cost c_guard(2k+64) via `PlaysProof.search_t`).
- **vs DIMCID was NOT blocked**: the action-refined set kernel
  `no_provable_tailToS_floor` handles a both-const searcher's tail when the
  forbidden action ≠ then-branch action (LegibleBot then-branch is .C, tail is
  plays L _ .D) — precedent `cd_no_provable_beta` in `CIMCIC/vs_DIMCID.lean`.
- Outcomes: (C,C) vs CooperateBot/MirrorBot/TitForTatBot/OBot/CupodTrollBot(∀j)/
  self/CIMCIC/DIMCID; (C,D) vs DefectBot/DBot/EBot. Legibility = unconditional
  cooperation ⇒ exploited by the defector-detectors.

**Still blocked (WaryBot's 6 rework cells)**: `.neg`-spine floor census missing —
census kernels hard-require `.plays` tails (`hplays`); WaryBot large-k vs
MirrorBot ((C,C) certified k=8/16 by prepass), OBot (expected flip (C,D), k=16
UNDETERMINED), self, CIMCIC, DIMCID, LegibleBot. See [[project-outcome-matrix-sheet-sync]].

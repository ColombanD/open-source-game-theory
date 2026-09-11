---
name: project-neg-guard-census-technique
description: .neg-guard exclusion SOLVED by modified-valuation soundness (SP/WV); TailTo neg-tail census is FALSE (contrapose)
metadata: 
  node_type: memory
  type: project
  originSessionId: df85cd50-954f-4c8c-a44f-b112fdf999ef
  modified: 2026-08-03T13:38:53.099Z
---

**WaryBot vs MirrorBot large-k fell 2026-07-30** — `outcome_WaryBot_vs_MirrorBot
(k fuel) : outcome (fuel+3) (WaryBot k) MirrorBot = some (.C, .C)` at ALL k (no
threshold), 3-standard-axiom footprint. Two transferable findings:

1. **Do NOT retry a TailTo-style census with a `.neg` tail** — the natural target
   `Pf K φ → K ≤ k → TailTo (.neg atom) φ → False` is FALSE: `Pf.implK` +
   `Pf.contrapose` manufacture `⊢ ¬(ψ → CA) → T` which is in the TailTo class and
   budget-affordable at large k. Any singleton-tail census dies on `contrapose`.

2. **The working technique: modified-valuation soundness ("SP/WV").** Define
   `SP k` = inductive closure of the target atom ("MirrorBot plays C vs WaryBot k")
   under sim/botSim lifts (invariant: opponent slot literally `WaryBot k`, by
   subst-preimage analysis — bare `.opp`/`.self` atoms aren't producible under
   non-atom frames), and `WV k` = `Formula.interp` with SP-atoms forced true.
   Show every Pf rule WV-sound by RAW mutual `Pf.rec` (39 arms — legitimate like
   `sound_upto`: the cross-IH through `PlaysProof.search_t`'s guard back-edge is
   required; budget induction does NOT close it since search_t's guard premise
   sits at budget k with no descent). WV(target refutation) = False ⇒ underivable
   at EVERY budget. Both semantic fixpoints are consistent, so plain soundness
   can't decide it — the valuation twist is what breaks the tie toward trust.

**Self-play CONFIRMED same day**: `outcome_WaryBot_vs_WaryBot (k fuel) = some (.C,.C)`
all k — base kill moves from the `sim` arm to `search_t` (cases-unification
instantiates the guard to `Pf k T'`, closed by the mutual structural IH); the
`searchBranch` leaf is WV-sound with no circularity (its box antecedent is raw
`Pf`, and under that never-realized hypothesis WaryBot really plays D). Both
integrated in `Theorems/WaryBot/` (SPMirror/SPSelf + instantiations in
Helpers.lean sub-namespace `PD.Theorems.WaryCensus`).
**Consolidated same day into `Base/ValuationSoundness.lean`**: ONE parametric
raw-recursor master lemma `wv_sound_upto (S ...)`; `sound_upto` MIGRATED onto it
(= empty-valuation instance, public statement byte-identical, 3-axiom footprint
verified); the two censuses are instantiations. Convention now: raw mutual
recursors ONLY in ProofSystem §4 + Base/ValuationSoundness.lean (CLAUDE.md
updated). Future valuation censuses: instantiate, never re-induct. Does NOT extend to
WaryBot vs OBot: there the refuted atom ("OBot plays C") is FALSE at large k, so
the refutation is TRUE — exclusion must be a COST-FLOOR argument (the certificate
crosses WaryBot's own failed search, paying `search_f`'s literal k), still open.
**LLM prover independently confirmed 2026-08-03** (run `WaryBot_vs_OBot_20260803T124727`,
3 episodes → `open_blocked`): outcome semantically (C,D) at large k (`wob_obot_plays_D_large`
proven, plus `wob_no_D_tail` via `no_provable_probeFirst_tail`); the wall is
`¬Pf k (.neg (plays OBot (WaryBot k) C))` — WV route dies on `wv_sound_upto`'s `h_ite`
obligation (OBot ite-headed, and forcing its C-atom is unsound since its cert concludes D);
hand TailTo-neg census dies on contrapose as predicted; double-neg obstruction means the
atomNeg route needs an OBot D-cert crossing WaryBot's failed search (the cost-floor lever).

Related: [[project-legiblebot-large-k-resolved]], [[project-floor-exclusion-blueprint]]

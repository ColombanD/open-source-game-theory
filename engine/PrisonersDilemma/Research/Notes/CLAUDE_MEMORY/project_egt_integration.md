---
name: project_egt_integration
description: "EGT layer (pd_runner.egt) integrated 2026-08-07 — the four traps that will bite (alpha=phases scale, \"N\"-state asymmetry, optional lrsnash, Nash cost)"
metadata: 
  node_type: memory
  type: project
  originSessionId: c36a8e10-b419-4585-8e14-c249175323ec
  modified: 2026-08-07T12:23:24.371Z
---

The standalone `egt-osgt-main` repo was ported into `app/src/pd_runner/egt/`
on 2026-08-07 (removed from the tree; recoverable from commit `bb51559`).
Four stages — ESS / invasion / faces / Nash — now run on the Lean-certified
matrix via `egt/ingest.py`, with a `(t, α)` sweep driver in `egt/pipeline.py`
and a web-app card behind `POST /egt/sweep`. Full map: CLAUDE.md "Phase 6".

**The four things that cost me time, none of them obvious from the code:**

1. **`--alphas phases` does not scale, though the theory says it should.**
   The `(t, α)` phase diagram IS piecewise constant, so "one α per phase" is
   exact. But at `t < 1` the softmax spreads the cooperation masses so nearly
   every (bot, signal) pair gets its own → ~|zoo|² phases per t. Measured on
   the default zoo: 507 grid points, 349 distinct matrices, ≈5h of Nash.
   Exactness was real; the unit of work was wrong. Default is an explicit α
   list (36 points → 16 matrices).

2. **A swept matrix NEVER contains the `"N"` (proven non-termination) state.**
   `tau_play` thresholds a cooperation mass and `cooperates()` tests `== "C"`,
   so an `"N"` base cell reads as not-cooperating and the lift emits a real
   `D`. **A TauBot always terminates even when the bot it lifts does not.**
   So the enlarged zoo analyses 15 types via the base path (MirrorBot dropped
   by `NonTerminationPolicy`) but 16 anywhere in a sweep. Do not compare
   base-vs-swept counts without accounting for this. Pinned by a test.

3. **Nash is the only expensive stage: ~50s per distinct matrix at N=11**
   (exact-rational vertex enumeration). Faces, which I expected to dominate at
   2036 supports, runs in <1s. This is why dedup-by-matrix is load-bearing
   rather than an optimization, and why `--stages ess,invasion,faces` is the
   fast path for exploration.

4. **`lrsnash` is a conda-forge binary `uv` cannot install**, and it is absent
   on this machine. It is the SECONDARY Nash solver that cross-checks
   pygambit. The pipeline degrades and records `cross_check_performed: false`
   — absence is never recorded as a passed check. Enable any time with
   `conda install -c conda-forge lrslib`; no code change needed.

Zoo selection reuses the existing `tau.matrix` `ZOOS` registry (4 zoos, not
the 2 I assumed), so a new zoo appears in the tau card, the EGT card, and
every stage CLI at once. See [[project_tau_v1a_explorer]].

---
name: project_egt_next_stages
description: EGT stages (iii) replicator + (iv) Moran — LANDED 2026-08-10; the headline is DupocBot uniquely stochastically stable at full transparency
metadata: 
  node_type: memory
  type: project
  originSessionId: c36a8e10-b419-4585-8e14-c249175323ec
  modified: 2026-08-10T12:19:24.696Z
---

**DONE 2026-08-10** (commit `9687def`). The gap Colomban asked to close — the
four earlier stages catalogue which resting points EXIST, these two say which
one a population actually REACHES — is now implemented as
`egt/replicator/` and `egt/moran/`. New code, not a port (the standalone repo's
`src/replicator/` and `src/moran/` were never written). See
[[project_egt_integration]] for the four ported stages.

**The result worth remembering.** On the default zoo at full transparency,
`DupocBot` (the Löbian cooperator) is UNIQUELY stochastically stable, and its
share of the long run rises with selection intensity: 20% → 55% → 82% → 89%
across the (M, β) sweep. At `t = 0` that collapses into a four-way tie
including `DefectBot`. So cooperation under transparency is not merely an
available equilibrium — it is where the population spends its time. This is
the strongest population-level statement the project can currently make.

**Four implementation facts that cost real time:**

1. **Basins must group by SUPPORT, not proximity.** The endpoints on this zoo
   land on a CONTINUUM of neutrally-stable rest points — 26 samples produced
   26 distinct endpoints (coordinate distances up to 0.45) sharing just 2
   supports. Proximity clustering reported 26 attractors at ~4% basin each:
   arithmetically true, a complete misreading. `Attractor.spread` exposes the
   continuum instead of hiding it.
2. **Integrator defaults matter enormously.** `dt=0.01, tol=1e-9` took 3-13s
   PER trajectory (~1h for 212 starts) and mislabelled a trajectory at speed
   1.5e-7 as unconverged. `dt=0.1, tol=1e-7, cap=50k` gives byte-identical
   attractor sets at 1.5s total — 60x faster. Verified equal, not assumed.
3. **Moran fixation MUST accumulate in log space.** The naive gamma product
   underflows to exactly 0 at moderate `beta*M`; measured a real rho of
   1.9e-10 that would have been reported as impossible, corrupting the
   stationary distribution downstream. Anchor test: at `beta=0`, rho is
   exactly `1/M` for ANY payoff matrix.
4. **Non-convergence is a FINDING.** RPS orbits forever → 30/31 unconverged,
   and those are never assigned to an attractor. Basin denominators are
   converged interior samples only; monoculture starts are counted separately
   (measure-zero).

Test-fixture note: `test_report.py` passes `replicator_samples=8`. At the
production default of 200 that one fixture took 14 minutes.

**Housekeeping** (still true): sweep artefacts under `app/generated/egt/runs/`
are NEVER auto-deleted and are gitignored; tests write to pytest tmp dirs.
Check the directory for runs I did not create before removing anything —
Colomban runs his own sweeps there. Same for `git add -A`: it once swept an
unrelated untracked research note into a commit. Stage explicitly.

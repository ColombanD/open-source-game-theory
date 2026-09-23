"""Evolutionary game theory over the Lean-verified outcome matrix.

Where the engine answers *what happens when bot X meets bot Y* (one match,
machine-checked) and the tau layer answers *what happens under graded
transparency* (Def 3, a `(t, α)` dial), this package answers **which bots
survive in a population of bots**.

Ported 2026-08-07 from the standalone `egt-osgt-main` repository. Four
analysis stages carried over essentially unchanged — they are ordinary EGT
mathematics and their tests validate them against textbook games
(Hawk-Dove, RPS, coordination), not against OSGT:

  - `static_analysis/` — pure-strategy ESS (Maynard-Smith two clauses)
  - `invasion/`        — invasion graphs `G>` / `G≥`, SCCs, condensation, cycles
  - `faces/`           — face equilibria: block solve, replicator Jacobian,
                         tangent-space eigenvalues
  - `nash/`            — extreme Nash equilibria, exact rationals, best-response
                         polytopes

What did NOT carry over is the original `src/ingest/` layer. That package
read a hand-transcribed CSV of action pairs and resolved two special cells
from a config file (the "red cell" `(CupodBot, DupocBot)`, unresolved in
Critch et al.; and `(MirrorBot, MirrorBot)`, non-terminating). Both problems
are already solved better upstream in this repo:

  - the matrix comes from the theorem library, not a transcription;
  - open cells are resolved by RESTRICTING THE ZOO (`tau.matrix`), so the
    matrix is total by construction rather than by imputation.

`ingest.py` is the replacement seam: action-pair cells -> real payoff matrix
`A`. It accepts a `TauMatrix` (the base matrix) or a `TournamentResult` (a
tau tournament at fixed `(t, α)`), which is what makes the `(t, α)` sweep
possible.

The inter-stage contract is unchanged: stage ii.a writes a numeric payoff
CSV, and stages ii.b-ii.d read it. That CSV now lives in a per-run directory
keyed by `(t, α, zoo)` rather than a fixed `results/ess/`.
"""

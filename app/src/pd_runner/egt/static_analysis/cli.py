"""Stage (ii.a): load matrix → enumerate ESS → write artefacts to the run dir."""

from __future__ import annotations

import argparse
from pathlib import Path

from pd_runner.egt.ingest import PayoffMatrix, payoff_matrix_from_tau_matrix
from pd_runner.egt.static_analysis.ess import enumerate_pure_ess, flag_suspect_cells
from pd_runner.egt.static_analysis.reporting import write_all

# Ordered pairs whose outcome is STIPULATED rather than proven. Verdicts that
# touch one are flagged `touches_suspect_cell` downstream. In the standalone
# repo this was the single Critch "red cell"; here it is whatever the selected
# zoo stipulates, so it is derived per-run rather than hardcoded.
# (This legacy default keeps the red cell as the worked example even though
# that cell is PROVEN since 2026-08-20 — real runs use `suspect_cells_for`.)
SUSPECT_CELLS = [
    ("CupodBot", "DupocBot"),
    ("DupocBot", "CupodBot"),
]


def suspect_cells_for(payoff: PayoffMatrix) -> list[tuple[str, str]]:
    """The run's stipulated cells, closed under transpose.

    A stipulated cell is one the Lean library has NOT proven; every ESS
    verdict that reads it is conditional, which is what the flag records.
    """
    out: set[tuple[str, str]] = set()
    for row, col in payoff.stipulated_cells:
        out.add((row, col))
        out.add((col, row))
    return sorted(out)


def build_assumptions(payoff: PayoffMatrix, atol: float) -> dict:
    """The ESS stage's assumptions block, rooted in the matrix's provenance."""
    return {
        "ess_definition": {
            "form": "Maynard Smith two-condition (pure-strategy, single-population, possibly asymmetric A)",
            "reference": "Sandholm 2010 Ch. 8; Weibull 1995 Def. 2.1",
            "clause_a": "A[i,i] > A[j,i]",
            "clause_b": "A[i,i] == A[j,i] AND A[i,j] > A[j,j]",
        },
        # Provenance of the matrix itself: zoo, PD convention, (t, α),
        # non-termination policy, stipulated cells. See egt.ingest.
        **payoff.assumptions(),
        "suspect_cells": [list(p) for p in suspect_cells_for(payoff)],
        "diagonal_undefined_policy": {
            "rule": (
                "If A[i,i] is non-finite, enumerate_pure_ess raises ValueError. "
                "The ingest layer raises earlier; this is defence in depth."
            ),
            "currently_triggered": False,
            "reason_currently_inactive": (
                "non-terminating cells are resolved by NonTerminationPolicy "
                "before A is built, so no diagonal sentinel survives ingest."
            ),
        },
        "tolerance": {
            "atol": atol,
            "rationale": (
                "payoffs are exact combinations of {b, -c, b-c, 0}; tolerance "
                "guards against float-arithmetic noise only"
            ),
        },
        "ess_pipeline_version": "0.2.0",
    }


def run_ess(payoff: PayoffMatrix, out_dir: Path, atol: float = 1e-12):
    """Enumerate pure ESS on `payoff` and write the stage's artefacts.

    Returns the `EssResult`. This is the library entry point the sweep driver
    and the API call; `main()` is the CLI wrapper around it.
    """
    bot_names = list(payoff.bots)
    result = enumerate_pure_ess(bot_names, payoff.A, atol=atol)
    result = flag_suspect_cells(result, suspect_cells_for(payoff))
    write_all(result, bot_names, payoff.A, build_assumptions(payoff, atol), out_dir)
    return result


def main() -> None:
    from pd_runner.tau.matrix import DEFAULT_ZOO, ZOOS, get_zoo

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--zoo", default=DEFAULT_ZOO, choices=sorted(ZOOS),
                   help="which tau sub-zoo to analyse")
    p.add_argument("--out", type=Path, default=Path("generated/egt/ess/"))
    p.add_argument("--atol", type=float, default=1e-12)
    args = p.parse_args()

    named = get_zoo(args.zoo)
    payoff = payoff_matrix_from_tau_matrix(named.load(), zoo=args.zoo)
    bot_names = list(payoff.bots)

    result = run_ess(payoff, args.out, atol=args.atol)

    n_ess = sum(1 for s in result.summary if s.is_ESS)
    print(f"Wrote artefacts to {args.out}/")
    print(f"  Pure ESS: {n_ess} / {len(bot_names)}")
    for s in result.summary:
        mark = "ESS" if s.is_ESS else "   "
        invs = (
            f" invaded by: {', '.join(s.failing_invaders)}"
            if s.failing_invaders else ""
        )
        print(f"  [{mark}] {s.type:<14}{invs}")


if __name__ == "__main__":
    main()

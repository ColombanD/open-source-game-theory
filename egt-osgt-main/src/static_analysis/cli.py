"""Entry point: load matrix → enumerate ESS → write artefacts under results/ess/."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import List, Mapping

from src.ingest.matrix_loader import load_payoff_matrix
from src.static_analysis.ess import enumerate_pure_ess, flag_suspect_cells
from src.static_analysis.reporting import write_all

SUSPECT_CELLS = [
    ("CupodBot", "DupocBot"),
    ("DupocBot", "CupodBot"),
]


def build_assumptions(
    config: Mapping, bot_names: List[str], atol: float
) -> dict:
    b = float(config["prisoners_dilemma"]["b"])
    c = float(config["prisoners_dilemma"]["c"])
    return {
        "ess_definition": {
            "form": "Maynard Smith two-condition (pure-strategy, single-population, possibly asymmetric A)",
            "reference": "Sandholm 2010 Ch. 8; Weibull 1995 Def. 2.1",
            "clause_a": "A[i,i] > A[j,i]",
            "clause_b": "A[i,i] == A[j,i] AND A[i,j] > A[j,j]",
        },
        "pd_payoffs": {
            "parametrisation": "(b, c) with b > c > 0",
            "b": b,
            "c": c,
            "implied_trps": {"T": b, "R": b - c, "P": 0.0, "S": -c},
            "convention": "row payoff: (D,C)=b, (C,C)=b-c, (D,D)=0, (C,D)=-c",
            "source": "config.json -> prisoners_dilemma",
        },
        "bot_names": list(bot_names),
        "excluded_types": {
            "MirrorBot": (
                "(MirrorBot, MirrorBot) is non-terminating in Critch et al. 2022; "
                "MirrorBot is excluded upstream from data/payoff_matrix.csv."
            ),
        },
        "undefined_cells_resolved": {
            "(CupodBot, DupocBot)": {
                "action_pair": config["undefined_outcomes"]["cupod_vs_dupoc"],
                "transpose_filled_by_loader": True,
                "source": "config.undefined_outcomes.cupod_vs_dupoc",
                "status": (
                    "unresolved in Critch et al. 2022 (red cell in payoff_matrix.png); "
                    "downstream verdicts that reference this cell are flagged as suspect"
                ),
            },
        },
        "diagonal_undefined_policy": {
            "rule": (
                "If A[i,i] is non-finite, enumerate_pure_ess raises ValueError. "
                "The loader currently raises earlier; this is a defence-in-depth check."
            ),
            "currently_triggered": False,
            "reason_currently_inactive": (
                "MirrorBot excluded; no diagonal sentinel survives the loader."
            ),
        },
        "lower_triangle_handling": {
            "input_state": (
                "data/payoff_matrix.csv is a full square matrix; no blank entries "
                "in the lower triangle."
            ),
            "action_taken": (
                "loader resolves blanks via configured undefined_outcomes and "
                "transposes the action pair for the lower triangle; pair-symmetry "
                "is not re-derived here."
            ),
        },
        "tolerance": {
            "atol": atol,
            "rationale": (
                "payoffs are exact combinations of {b, -c, b-c, 0}; tolerance "
                "guards against float-arithmetic noise only"
            ),
        },
        "seed": config.get("seed"),
        "ess_pipeline_version": "0.1.0",
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--csv", type=Path, default=Path("data/payoff_matrix.csv"))
    p.add_argument("--config", type=Path, default=Path("config.json"))
    p.add_argument("--out", type=Path, default=Path("results/ess/"))
    p.add_argument("--atol", type=float, default=1e-12)
    args = p.parse_args()

    bot_names, A = load_payoff_matrix(args.csv, args.config)
    with open(args.config) as f:
        config = json.load(f)

    result = enumerate_pure_ess(bot_names, A, atol=args.atol)
    result = flag_suspect_cells(result, SUSPECT_CELLS)

    assumptions = build_assumptions(config, bot_names, args.atol)
    write_all(result, bot_names, A, assumptions, args.out)

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

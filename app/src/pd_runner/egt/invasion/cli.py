"""Entry point: load numeric A → build G>/G≥ → analyse → cross-check ESS
→ write CSV/JSON/MD + GEXF + SVG/PNG under results/invasion/.
"""

from __future__ import annotations

import argparse
import importlib.metadata as md
from pathlib import Path
from typing import Optional

import networkx as nx  # type: ignore
import numpy as np  # type: ignore

from .analysis import compute_readouts
from .cross_check import compare_against_ess
from .graph import SUSPECT_CELLS, build_strict, build_weak
from .loader import load_numeric_A
from .reporting import write_all
from .viz import render_condensation, render_invasion


def _build_assumptions(
    load_result,
    suspect_cells,
    atol: float,
    cycle_cap: int,
    layout_backend: str,
    condensation_layout_backend: str,
    seed: int,
) -> dict:
    versions = {
        "networkx": nx.__version__,
        "numpy": np.__version__,
    }
    try:
        versions["matplotlib"] = md.version("matplotlib")
    except Exception:
        pass

    inherited = load_result.inherited_assumptions or {}
    pd = inherited.get("pd_payoffs", {})
    out = {
        "edge_definition": {
            "strict": "G>: i -> j iff A[i, j] >  A[j, j]",
            "weak":   "G≥: i -> j iff A[i, j] >= A[j, j]",
            "tie_set": "T = E(G≥) \\ E(G>) — pairs where ESS clause (b) bites",
        },
        "pd_payoffs": pd,
        "bot_names": load_result.bot_names,
        "numeric_matrix_source": load_result.source,
        "cross_check_against_ingest": {
            "performed": load_result.cross_checked,
            "max_abs_diff": load_result.cross_check_max_abs_diff,
        },
        "suspect_cells": [list(p) for p in suspect_cells],
        "diagonal_handling": (
            inherited.get("diagonal_undefined_policy")
            or inherited.get("excluded_types")
            or {"note": "diagonal must be finite; otherwise build_strict raises"}
        ),
        "tolerance": {"atol": atol, "rationale": "guards float-noise; payoffs exact"},
        "cycle_cap": cycle_cap,
        "layout_backend_graph": layout_backend,
        "layout_backend_condensation": condensation_layout_backend,
        "seed": seed,
        "library_versions": versions,
        "invasion_pipeline_version": "0.1.0",
    }
    return out


def run_invasion(
    payoff,
    numeric_csv: Path,
    out_dir: Path,
    ess_summary: Optional[Path] = None,
    inherited_assumptions: Optional[Path] = None,
    atol: float = 1e-12,
    cycle_cap: int = 10_000,
    seed: int = 20260514,
    render: bool = True,
):
    """Build and analyse the invasion graphs; write the stage's artefacts.

    `payoff` is the run's `egt.ingest.PayoffMatrix`, used both for the
    defence-in-depth cross-check against `numeric_csv` and for the run's
    stipulated (suspect) cells. `render=False` skips the matplotlib figures,
    which dominate the runtime in a sweep.
    """
    from pd_runner.egt.static_analysis.cli import suspect_cells_for

    load_result = load_numeric_A(
        numeric_csv=numeric_csv,
        rebuilt=payoff,
        inherited_assumptions_path=inherited_assumptions,
        atol=atol,
    )
    names, A = load_result.bot_names, load_result.A
    suspect_cells = suspect_cells_for(payoff)

    G_strict = build_strict(names, A, suspect_cells, atol=atol)
    G_weak = build_weak(names, A, suspect_cells, atol=atol)
    analysis = compute_readouts(G_strict, G_weak, cycle_cap=cycle_cap)

    ess_summary_path = ess_summary if (ess_summary and ess_summary.exists()) else None
    agreements = compare_against_ess(G_strict, G_weak, ess_summary_path)

    out_dir.mkdir(parents=True, exist_ok=True)

    if render:
        layout_backend = render_invasion(G_strict, G_weak, analysis, out_dir, seed=seed)
        cond_backend = render_condensation(G_strict, analysis, out_dir, seed=seed)
    else:
        layout_backend = cond_backend = "skipped"

    assumptions = _build_assumptions(
        load_result, suspect_cells, atol, cycle_cap,
        layout_backend, cond_backend, seed,
    )
    write_all(
        G_strict, G_weak, analysis, agreements, A, assumptions,
        ess_summary_path, out_dir,
    )
    return G_strict, G_weak, analysis, agreements, layout_backend


def main() -> None:
    from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
    from pd_runner.tau.matrix import DEFAULT_ZOO, ZOOS, get_zoo

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--zoo", default=DEFAULT_ZOO, choices=sorted(ZOOS),
                   help="which tau sub-zoo to analyse (must match the ESS run)")
    p.add_argument("--numeric-csv", type=Path,
                   default=Path("generated/egt/ess/payoff_matrix_numeric.csv"))
    p.add_argument("--inherited-assumptions", type=Path,
                   default=Path("generated/egt/ess/assumptions.json"))
    p.add_argument("--ess-summary", type=Path,
                   default=Path("generated/egt/ess/ess_summary.csv"))
    p.add_argument("--out", type=Path, default=Path("generated/egt/invasion/"))
    p.add_argument("--atol", type=float, default=1e-12)
    p.add_argument("--cycle-cap", type=int, default=10_000)
    p.add_argument("--seed", type=int, default=20260514)
    args = p.parse_args()

    payoff = payoff_matrix_from_tau_matrix(get_zoo(args.zoo).load(), zoo=args.zoo)
    names = list(payoff.bots)

    G_strict, G_weak, analysis, agreements, layout_backend = run_invasion(
        payoff, args.numeric_csv, args.out,
        ess_summary=args.ess_summary,
        inherited_assumptions=args.inherited_assumptions,
        atol=args.atol, cycle_cap=args.cycle_cap, seed=args.seed,
    )

    print(f"Wrote artefacts to {args.out}/")
    print(f"  N = {len(names)}, |E(G>)| = {G_strict.number_of_edges()}, "
          f"|E(G≥)| = {G_weak.number_of_edges()}")
    print(f"  SCCs: {len(analysis.sccs)}; terminal SCCs: {analysis.terminal_sccs}")
    print(f"  cycles: {analysis.cycles.n_cycles_total} "
          f"(cap_hit={analysis.cycles.cap_hit})")
    print(f"  layout backend: {layout_backend}")
    n_disagree = sum(1 for a in agreements if a.agrees_with_ess is False)
    print(f"  cross-check disagreements: {n_disagree}")


if __name__ == "__main__":
    main()

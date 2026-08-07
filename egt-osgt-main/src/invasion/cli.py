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


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--numeric-csv", type=Path,
                   default=Path("results/ess/payoff_matrix_numeric.csv"))
    p.add_argument("--raw-csv", type=Path,
                   default=Path("data/payoff_matrix.csv"))
    p.add_argument("--config", type=Path, default=Path("config.json"))
    p.add_argument("--inherited-assumptions", type=Path,
                   default=Path("results/ess/assumptions.json"))
    p.add_argument("--ess-summary", type=Path,
                   default=Path("results/ess/ess_summary.csv"))
    p.add_argument("--out", type=Path, default=Path("results/invasion/"))
    p.add_argument("--atol", type=float, default=1e-12)
    p.add_argument("--cycle-cap", type=int, default=10_000)
    p.add_argument("--seed", type=int, default=20260514)
    args = p.parse_args()

    load_result = load_numeric_A(
        numeric_csv=args.numeric_csv,
        raw_csv=args.raw_csv,
        config=args.config,
        inherited_assumptions_path=args.inherited_assumptions,
        atol=args.atol,
    )
    names, A = load_result.bot_names, load_result.A

    G_strict = build_strict(names, A, SUSPECT_CELLS, atol=args.atol)
    G_weak = build_weak(names, A, SUSPECT_CELLS, atol=args.atol)
    analysis = compute_readouts(G_strict, G_weak, cycle_cap=args.cycle_cap)

    ess_summary_path: Optional[Path] = (
        args.ess_summary if args.ess_summary.exists() else None
    )
    agreements = compare_against_ess(G_strict, G_weak, ess_summary_path)

    args.out.mkdir(parents=True, exist_ok=True)

    layout_backend = render_invasion(
        G_strict, G_weak, analysis, args.out, seed=args.seed
    )
    cond_backend = render_condensation(
        G_strict, analysis, args.out, seed=args.seed
    )

    assumptions = _build_assumptions(
        load_result, SUSPECT_CELLS, args.atol, args.cycle_cap,
        layout_backend, cond_backend, args.seed,
    )
    write_all(
        G_strict, G_weak, analysis, agreements, A, assumptions,
        ess_summary_path, args.out,
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

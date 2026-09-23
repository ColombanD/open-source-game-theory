"""Stage (iii) runner: basins of attraction for one payoff matrix."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np  # type: ignore

from .basins import estimate_basins


def run_replicator(
    numeric_matrix: Path,
    out_dir: Path,
    inherited_assumptions: Path | None = None,
    n_samples: int = 200,
    seed: int = 20260514,
    dt: float = 0.1,
    max_steps: int = 50_000,
):
    """Sample the simplex, integrate, cluster, and write the artefacts."""
    from pd_runner.egt.faces.io import load_inherited_assumptions, load_numeric_matrix

    names, A = load_numeric_matrix(numeric_matrix)
    inherited = load_inherited_assumptions(inherited_assumptions)

    result = estimate_basins(
        A, names, n_samples=n_samples, seed=seed, dt=dt, max_steps=max_steps
    )

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    payload = result.summary()
    (out_dir / "basins.json").write_text(json.dumps(payload, indent=2))

    (out_dir / "assumptions.json").write_text(json.dumps({
        "stage": "replicator_dynamics",
        "replicator_pipeline_version": "0.1.0",
        "numeric_matrix_source": str(numeric_matrix),
        "equation": "xdot_i = x_i * ((A x)_i - x^T A x)",
        "integrator": {
            "method": "fixed-step RK4, projected onto the simplex each step",
            "dt": dt,
            "max_steps": max_steps,
            "convergence": "max|xdot| < 1e-7",
        },
        "sampling": {
            "interior": "symmetric Dirichlet(1) — uniform ON the simplex, not "
                        "normalised uniform draws (which concentrate at the centre)",
            "n_samples": n_samples,
            "seed": seed,
            "vertices": "all N monocultures, counted separately from the "
                        "basin fractions (a measure-zero set)",
        },
        "unconverged_policy": (
            "a trajectory that does not reach the tolerance is NEVER assigned "
            "to an attractor; it is counted in n_unconverged. Cyclic games "
            "(e.g. rock-paper-scissors) legitimately produce mostly "
            "unconverged runs, which is a finding, not a failure."
        ),
        "basin_denominator": "converged INTERIOR samples only",
        "pd_payoffs": (inherited or {}).get("pd_payoffs", {}),
        "tau": (inherited or {}).get("tau", {}),
        "zoo": (inherited or {}).get("zoo"),
    }, indent=2))

    lines = [
        "# Replicator dynamics — basins of attraction",
        "",
        f"- Numeric matrix: `{numeric_matrix}`",
        f"- Types: **{len(names)}**",
        f"- Interior samples: **{result.n_interior_samples}** "
        f"({result.n_interior_converged} converged)",
        f"- Unconverged trajectories: **{result.n_unconverged}**",
        "",
    ]
    if result.n_unconverged:
        lines += [
            f"> **{result.n_unconverged} trajectories did not converge.** They "
            "are excluded from every basin fraction below. A game with closed "
            "orbits (rock-paper-scissors and its relatives) produces exactly "
            "this: the population cycles forever rather than settling, which "
            "is a result about the dynamics, not a numerical failure.",
            "",
        ]
    lines += ["## Attractors", "",
              "| support | basin | interior | from monocultures |",
              "| --- | --- | --- | --- |"]
    for a in sorted(result.attractors, key=lambda a: -a.n_interior):
        support = ", ".join(a.support(names)) or "—"
        sources = ", ".join(a.vertex_sources) or "—"
        lines.append(
            f"| {support} | {result.basin_fraction(a):.1%} | "
            f"{a.n_interior} | {sources} |"
        )
    (out_dir / "report.md").write_text("\n".join(lines) + "\n")

    return result

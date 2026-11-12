"""Stage (iii) runner: basins of attraction for one payoff matrix."""

from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

from .basins import ExtremeEquilibrium, estimate_basins
from .dynamics import ATOL, HORIZON, MAX_HORIZON, MAX_RHS_EVALS, RTOL, TOL

REPLICATOR_PIPELINE_VERSION = "0.2.0"  # 0.1.0: fixed-step RK4, speed test (until 2026-11-10)


def load_extreme_equilibria(path: Path, names: list[str]) -> list[ExtremeEquilibrium] | None:
    """The Nash stage's `equilibria.jsonl` as `(xi, eta, component_id)`, or None if absent.

    Refuses a file whose strategies are not over `names` in this order: a
    stale Nash run of another matrix must not label this matrix's endpoints.
    """
    path = Path(path)
    if not path.exists():
        return None
    out: list[ExtremeEquilibrium] = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        xi = [Fraction(v) for v in row["xi_rational"]]
        eta = [Fraction(v) for v in row["eta_rational"]]
        if len(xi) != len(names) or len(eta) != len(names):
            raise ValueError(f"{path}: equilibria over {len(xi)} types, the matrix has {len(names)}")
        if [names[i] for i in row["support_row"]] != list(row["support_row_names"]):
            raise ValueError(f"{path}: the equilibria are not over this matrix's types")
        out.append((xi, eta, int(row["component_id"])))
    return out


def run_replicator(
    numeric_matrix: Path,
    out_dir: Path,
    inherited_assumptions: Path | None = None,
    n_samples: int = 1000,
    seed: int = 20260514,
    horizon: float = HORIZON,
    max_horizon: float = MAX_HORIZON,
    tol: float = TOL,
    max_rhs_evals: int = MAX_RHS_EVALS,
    equilibria_jsonl: Path | None = None,
):
    """Sample the simplex, integrate, group, and write the artefacts.

    `equilibria_jsonl` — the Nash stage's `equilibria.jsonl` for the SAME
    matrix — turns on the matching of endpoints to Nash components; without
    it (a Nash-free sweep) the basins are by support only.
    """
    from pd_runner.egt.faces.io import load_inherited_assumptions, load_numeric_matrix

    names, A = load_numeric_matrix(numeric_matrix)
    inherited = load_inherited_assumptions(inherited_assumptions)
    equilibria = (load_extreme_equilibria(equilibria_jsonl, list(names))
                  if equilibria_jsonl is not None else None)

    result = estimate_basins(
        A, names, n_samples=n_samples, seed=seed, horizon=horizon,
        max_horizon=max_horizon, tol=tol, max_rhs_evals=max_rhs_evals,
        equilibria=equilibria,
    )

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    payload = result.summary()
    (out_dir / "basins.json").write_text(json.dumps(payload, indent=2))

    (out_dir / "assumptions.json").write_text(json.dumps({
        "stage": "replicator_dynamics",
        "replicator_pipeline_version": REPLICATOR_PIPELINE_VERSION,
        "numeric_matrix_source": str(numeric_matrix),
        "equation": "xdot_i = x_i * ((A x)_i - x^T A x)",
        "integrator": {
            "method": "LSODA on log-shares z_i = log x_i (zdot_i = g_i(x), x = softmax(z))",
            "rtol": RTOL,
            "atol": ATOL,
            "horizon": horizon,
            "max_horizon": max_horizon,
            "max_rhs_evals_per_start": max_rhs_evals,
            "convergence": (
                f"at both H/2 and H the state is a symmetric Nash equilibrium up to {tol:g} "
                "(no type grows faster than tol; every type is absent, x_i < tol, or ties the "
                "best reply, g_i >= -tol), with the same absent and tied sets, and it moved "
                "less than tol in between. A start that fails at H is integrated on to 100 H, "
                "up to max_horizon."
            ),
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
            "a trajectory that fails the convergence test is NEVER assigned "
            "to an attractor; it is counted in n_unconverged (n_budget_exhausted "
            "of them ran out of evaluations — cycles). Cyclic games legitimately "
            "produce unconverged runs, which is a finding, not a failure."
        ),
        "metastable_policy": (
            "a converged start whose rest point has an absent type that ties the best "
            "reply and earns more against itself than the residents earn against it is "
            "flagged metastable: that type invades at second order, so the exact dynamics "
            "leaves the rest point, after a time that grows without bound as the invader's "
            "starting share shrinks. Such starts are integrated to max_horizon; a metastable "
            "basin is a statement about that horizon, not an attractor."
        ),
        "basin_denominator": "ALL interior samples integrated (unconverged starts are their own share)",
        "cycling_policy": (
            "a game in which at least half of the first 100 interior starts run out of evaluations is a cycling game: "
            "the remaining starts are not integrated (truncated_cycling in basins.json), and "
            "n_interior_samples is the number integrated"
        ),
        "nash_components": (
            f"endpoints matched to the components of {equilibria_jsonl}"
            if equilibria is not None else "not matched (no Nash equilibria supplied)"
        ),
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
        f"({result.n_interior_converged} converged, horizon {horizon:g} to {max_horizon:g})",
        f"- Unconverged trajectories: **{result.n_unconverged}**"
        + (f" ({result.n_budget_exhausted} ran out of evaluations)"
           if result.n_budget_exhausted else ""),
        f"- Metastable (converged to a rest point the dynamics leaves): "
        f"**{result.n_metastable}**",
        "",
    ]
    if result.truncated_cycling:
        lines += [
            f"> **Cycling game.** {result.n_budget_exhausted} of the first {result.n_interior_samples} "
            f"interior starts ran out of evaluations, so the remaining "
            f"{result.n_interior_requested - result.n_interior_samples} were not integrated.",
            "",
        ]
    if result.n_unconverged:
        lines += [
            f"> **{result.n_unconverged} trajectories did not converge.** They "
            "are assigned to no attractor and count against every basin below. "
            "A game with closed orbits (rock-paper-scissors and its relatives) "
            "produces exactly this: the population cycles forever rather than "
            "settling, which is a result about the dynamics, not a numerical "
            "failure.",
            "",
        ]
    if result.has_components:
        lines += ["## Basins by Nash component", "",
                  "| component | basin | 95% CI | interior | metastable | bots |",
                  "| --- | --- | --- | --- | --- | --- |"]
        for c in result.component_basins():
            lo, hi = c["basin_ci95"]
            lines.append(
                f"| {c['component_id']} | {c['basin_fraction']:.1%} | "
                f"{lo:.1%} to {hi:.1%} | {c['n_interior']} | {c['n_metastable']} | "
                f"{', '.join(c['bots'])} |"
            )
        lines.append("")
    lines += ["## Attractors (by support)", "",
              "| support | basin | interior | metastable (invaded by) | from monocultures |",
              "| --- | --- | --- | --- | --- |"]
    for a in sorted(result.attractors, key=lambda a: -a.n_interior):
        support = ", ".join(a.support(names)) or "—"
        sources = ", ".join(a.vertex_sources) or "—"
        invaded = (f"{a.n_metastable} ({', '.join(names[i] for i in sorted(a.invaders))})"
                   if a.n_metastable else "—")
        lines.append(
            f"| {support} | {result.basin_fraction(a):.1%} | "
            f"{a.n_interior} | {invaded} | {sources} |"
        )
    (out_dir / "report.md").write_text("\n".join(lines) + "\n")

    return result

"""Stage (iv) runner: a Moran sweep over population size and selection."""

from __future__ import annotations

import json
from pathlib import Path

from .stationary import analyse

# Defaults span the interesting range: M from "drift dominates" to "selection
# dominates", beta from near-neutral to strong. Both are dials the reader is
# meant to move, so both are recorded in the assumptions.
DEFAULT_POPULATIONS: tuple[int, ...] = (10, 50, 100)
DEFAULT_BETAS: tuple[float, ...] = (0.01, 0.1, 1.0)


def run_moran(
    numeric_matrix: Path,
    out_dir: Path,
    inherited_assumptions: Path | None = None,
    populations: tuple[int, ...] = DEFAULT_POPULATIONS,
    betas: tuple[float, ...] = DEFAULT_BETAS,
):
    """Analyse every `(M, beta)` point and write the artefacts."""
    from pd_runner.egt.faces.io import load_inherited_assumptions, load_numeric_matrix

    names, A = load_numeric_matrix(numeric_matrix)
    inherited = load_inherited_assumptions(inherited_assumptions)

    results = [
        analyse(A, names, population=M, beta=beta)
        for M in populations
        for beta in betas
    ]

    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "stationary.json").write_text(json.dumps({
        "names": names,
        "points": [r.summary() for r in results],
    }, indent=2))

    (out_dir / "assumptions.json").write_text(json.dumps({
        "stage": "moran_process",
        "moran_pipeline_version": "0.1.0",
        "numeric_matrix_source": str(numeric_matrix),
        "process": {
            "form": "frequency-dependent Moran, birth-death, one replacement "
                    "per step",
            "fitness": "exponential, f = exp(beta * payoff) — positive for any "
                       "payoff, so the matrix needs no shift",
            "self_interaction": "excluded; payoffs use the M-1 denominator",
        },
        "fixation": {
            "method": "closed form for the 1-D birth-death chain",
            "numerics": "accumulated in LOG space — the gamma products "
                        "underflow to zero for moderate beta*M, which would "
                        "report a rare fixation as impossible",
        },
        "stationary": {
            "limit": "small-mutation limit: each mutation fixates or dies "
                     "before the next arrives, so the population is a "
                     "monoculture almost always",
            "chain": "P[j->i] = rho(i->j)/(N-1) for i != j",
            "method": "left eigenvector for eigenvalue 1",
            "stable_threshold": "mass >= 1.5 / N (the raw distribution is "
                                "reported too, so another cut can be applied)",
        },
        "sweep": {"populations": list(populations), "betas": list(betas)},
        "pd_payoffs": (inherited or {}).get("pd_payoffs", {}),
        "tau": (inherited or {}).get("tau", {}),
        "zoo": (inherited or {}).get("zoo"),
    }, indent=2))

    lines = [
        "# Moran process — finite-population outcomes",
        "",
        f"- Numeric matrix: `{numeric_matrix}`",
        f"- Types: **{len(names)}**",
        f"- Sweep: M ∈ {list(populations)}, β ∈ {list(betas)}",
        "",
        "Stochastic stability is where the population spends its TIME, which "
        "can disagree with every earlier stage: a type that is no ESS and sits "
        "inside a cycle can still dominate the long run if it is hard to "
        "invade and easy to reach.",
        "",
        "| M | β | stochastically stable | top of the stationary distribution |",
        "| --- | --- | --- | --- |",
    ]
    for r in results:
        stable = ", ".join(r.stochastically_stable()) or "— (no type above the cut)"
        top = ", ".join(f"{n} {p:.1%}" for n, p in r.ranked()[:3])
        flag = "" if r.converged else " ⚠ solve did not converge"
        lines.append(f"| {r.population} | {r.beta:g} | {stable} | {top}{flag} |")
    (out_dir / "report.md").write_text("\n".join(lines) + "\n")

    return results

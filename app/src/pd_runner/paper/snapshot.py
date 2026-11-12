"""Rebuild `app/paper_results/` from the sweep output.

    uv run python -m pd_runner.paper.snapshot [--from DIR] [--out DIR]

`--from` is where the sweeps wrote (`scripts/rerun_paper_experiments.sh`; default `app/generated`), `--out` the
snapshot folder (default `app/paper_results`). Writes

  full_transparency/<library>__<side>.json    one game each: payoff matrix, extreme equilibria with their
                                              components, the replicator stage's summary, and the same integration
                                              restricted to the 1,000 uniformly drawn starts (`uniform_starts`)
  partial_transparency/<family>_<side>.json   one line per distinct game of a fine-grid sweep: its grid points, the
                                              cooperation of each equilibrium component, where the sampled
                                              populations end, and their long-run cooperation where they cycle

Two things are computed here and not by the sweeps.

The replicator stage integrates 1,001 interior starts: the centre of the simplex, then 1,000 draws from the uniform
distribution on it. The paper reports the 1,000 draws. `uniform_starts` re-integrates all 1,001 exactly as the stage
does, checks that the result matches the stage's own counts, and then drops the centre.

Where more than half of the sampled populations of a game never settle, the stage stops after 100 starts and
reports them as unconverged. For those games `cycle` is the cooperation the populations average in the long run:
40 uniformly drawn starts integrated to time 30,000, Pr[(C,C)] averaged over [10,000, 30,000].
"""
from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

from pd_runner.egt.faces.io import load_numeric_matrix
from pd_runner.egt.replicator.dynamics import growth_rates, integrate, simplex_samples, softmax
from pd_runner.paper import FULL_TRANSPARENCY_GAMES, PARTIAL_TRANSPARENCY_SWEEPS, RESULTS

APP = Path(__file__).resolve().parents[3]
MUTUAL_COOPERATION_PAYOFF = 2.0      # R: in the paper's payoffs, (C, C) is the only outcome that pays 2
CYCLE_STARTS, CYCLE_SEED, CYCLE_BURN_IN, CYCLE_END = 40, 20260514, 10_000, 30_000


def _json(path: Path):
    return json.loads(path.read_text())


def _matrix(run_dir: Path) -> tuple[list[str], np.ndarray]:
    names, A = load_numeric_matrix(run_dir / "ess" / "payoff_matrix_numeric.csv")
    return list(names), np.asarray(A, float)


def _equilibria(run_dir: Path, names: list[str]) -> list[dict]:
    """The extreme equilibria of a run, exact: each player's mix over its support, cooperation, payoffs, component."""
    out = []
    for line in (run_dir / "nash" / "latest" / "equilibria.jsonl").read_text().splitlines():
        r = json.loads(line)

        def mix(key: str) -> dict[str, str]:
            assert len(r[key]) == len(names)
            return {names[i]: str(Fraction(p)) for i, p in enumerate(r[key]) if Fraction(p) != 0}

        out.append({
            "component": r["component_id"],
            "row": mix("xi_rational"), "col": mix("eta_rational"),
            "cooperation": str(Fraction(r["cooperation_rate_rational"])),
            "row_payoff": str(Fraction(r["u_rational"])), "col_payoff": str(Fraction(r["v_rational"])),
        })
    return out


def _uniform_starts(names: list[str], A: np.ndarray, basins: dict) -> dict:
    """Where the 1,000 uniformly drawn starts end (the stage's 1,001 interior starts minus the centre)."""
    component_of = {frozenset(a["support"]): a["components"] for a in basins["attractors"]}
    n_draws = basins["n_interior_requested"] - 1
    starts = simplex_samples(len(names), n_draws, basins["seed"], include_vertices=False, include_uniform=True)
    tol = basins["tol"]
    ends = []
    for x0 in starts:
        tr = integrate(A, x0, horizon=basins["horizon"], max_horizon=basins["max_horizon"], tol=tol)
        support = frozenset(names[i] for i in np.flatnonzero(tr.x >= tol))
        ends.append((tr, support))

    def tally(items) -> dict:
        by_support, by_component = Counter(), Counter()
        invadable, unconverged = Counter(), 0
        for tr, support in items:
            if not tr.converged:
                unconverged += 1
                continue
            by_support[support] += 1
            (cid,) = component_of[support]
            by_component[cid] += 1
            invadable[cid] += int(tr.metastable)
        return {"by_support": by_support, "by_component": by_component, "invadable": invadable,
                "unconverged": unconverged}

    # The re-integration must be the stage's own computation: same counts over all 1,001 starts.
    everything = tally(ends)
    stored = {frozenset(a["support"]): a["n_interior"] for a in basins["attractors"] if a["n_interior"]}
    assert dict(everything["by_support"]) == stored, "re-integration disagrees with the replicator stage"
    assert everything["unconverged"] == basins["n_unconverged"]

    draws = tally(ends[1:])
    converged = [tr for tr, _ in ends[1:] if tr.converged]
    final = np.array([tr.x for tr in converged])
    order = sorted(draws["by_support"].items(), key=lambda kv: (-kv[1], sorted(kv[0])))
    return {
        "n": n_draws, "seed": basins["seed"],
        "n_converged": len(converged), "n_unconverged": draws["unconverged"],
        "by_component": [{"component": cid, "n": k, "n_at_last_horizon_with_an_invader": draws["invadable"][cid]}
                         for cid, k in sorted(draws["by_component"].items())],
        "by_support": [{"present": sorted(s), "n": k} for s, k in order],
        "final_share_range": {name: [round(float(final[:, i].min()), 6), round(float(final[:, i].max()), 6)]
                              for i, name in enumerate(names)},
        "centre_start_ends_on": sorted(ends[0][1]),
    }


def full_transparency_game(runs: Path, zoo: str, side: str) -> dict:
    """The game of a library at full transparency: the one run of that library and side that covers t = 1."""
    prefix = f"{zoo}_sprime_" + ("" if side == "engine_side" else f"{side}_")
    found = {}
    for run_dir in sorted(runs.glob(prefix + "t100_a*")):
        summary = _json(run_dir / "summary.json")
        if (summary["zoo"], summary["floor_policy"], summary["family"]) != (zoo, side, "behavioral"):
            continue
        if any(t == 1.0 and a > 0 for t, a in summary["grid_points"]):   # caution 0 is a different, degenerate game
            found[summary["fingerprint"]] = (run_dir, summary)
    (run_dir, summary), = found.values()
    names, A = _matrix(run_dir)
    assert names == summary["bots"]
    basins = _json(run_dir / "replicator" / "basins.json")
    keep = ["n_interior_samples", "n_interior_converged", "n_unconverged", "n_budget_exhausted", "n_metastable",
            "seed", "horizon", "max_horizon", "tol", "horizons_reached"]
    return {
        "library": zoo, "side": side, "matrix_fingerprint": summary["fingerprint"],
        "cell_source": summary["cell_source"],
        "programs": names,
        "hinge_cells": summary["floor_cells"],
        "payoff_matrix": [[int(v) if float(v).is_integer() else float(v) for v in row] for row in A],
        "equilibria": _equilibria(run_dir, names),
        "replicator_stage": {
            **{k: basins[k] for k in keep},
            "components": basins["components"],
            "supports_reached": [{k: a[k] for k in ("support", "n_interior", "n_metastable", "invaders", "components")}
                                 for a in basins["attractors"] if a["n_interior"]],
        },
        "uniform_starts": _uniform_starts(names, A, basins),
    }


def _cycle(run_dir: Path) -> dict:
    """Long-run cooperation of the populations of a game in which they do not settle."""
    names, A = _matrix(run_dir)
    mutual = (A == MUTUAL_COOPERATION_PAYOFF).astype(float)

    def field(_, z):
        return growth_rates(A, softmax(z))

    averages, present = [], set()
    for x0 in simplex_samples(len(names), CYCLE_STARTS, CYCLE_SEED, include_vertices=False, include_uniform=False):
        sol = solve_ivp(field, (0, CYCLE_END), np.log(x0), method="LSODA",
                        t_eval=np.linspace(CYCLE_BURN_IN, CYCLE_END, 8001), rtol=1e-9, atol=1e-11)
        X = np.array([softmax(z) for z in sol.y.T])
        averages.append(float(np.mean(np.einsum("ti,ij,tj->t", X, mutual, X))))
        present |= {names[i] for i in np.flatnonzero(X.mean(axis=0) > 1e-3)}
    return {"time_average_cooperation": float(np.mean(averages)), "min": float(min(averages)),
            "max": float(max(averages)), "programs": sorted(present)}


def partial_transparency_sweep(sweep_dir: Path) -> list[dict]:
    games = []
    for summary_path in sorted((sweep_dir / "runs").glob("*/summary.json")):
        run_dir = summary_path.parent
        summary = _json(summary_path)
        levels: dict[int, set] = defaultdict(set)
        sizes: Counter = Counter()
        for line in (run_dir / "nash" / "latest" / "equilibria.jsonl").read_text().splitlines():
            r = json.loads(line)
            levels[r["component_id"]].add(Fraction(r["cooperation_rate_rational"]))
            sizes[r["component_id"]] += 1
        basins = _json(run_dir / "replicator" / "basins.json")
        game = {
            "run": summary["run"],
            "grid_points": sorted([round(t, 2), round(a, 2)] for t, a in summary["grid_points"]),
            "components": [{"id": cid, "n_extreme": sizes[cid], "cooperation": [str(x) for x in sorted(levels[cid])]}
                           for cid in sorted(levels)],
            "replicator": {
                "n": basins["n_interior_samples"],
                "reached": [{"id": c["component_id"], "n": c["n_interior"], "n_with_an_invader": c["n_metastable"]}
                            for c in basins["components"]],
                "n_unconverged": basins["n_unconverged"], "n_budget_exhausted": basins["n_budget_exhausted"],
                "n_unlocated": basins["n_unlocated"], "truncated_cycling": basins["truncated_cycling"],
            },
        }
        if 2 * basins["n_unconverged"] > basins["n_interior_samples"]:
            game["cycle"] = _cycle(run_dir)
        games.append(game)
    games.sort(key=lambda g: (g["grid_points"][0][1], g["grid_points"][0][0]))
    return games


def main() -> None:
    parser = argparse.ArgumentParser(description="Rebuild the tracked snapshot of the paper's results.")
    parser.add_argument("--from", dest="source", type=Path, default=APP / "generated",
                        help="where the sweeps wrote: <DIR>/egt/runs and <DIR>/egt_fine/<sweep>/runs")
    parser.add_argument("--out", type=Path, default=RESULTS)
    args = parser.parse_args()
    (args.out / "full_transparency").mkdir(parents=True, exist_ok=True)
    (args.out / "partial_transparency").mkdir(parents=True, exist_ok=True)
    for zoo, side in FULL_TRANSPARENCY_GAMES:
        game = full_transparency_game(args.source / "egt" / "runs", zoo, side)
        path = args.out / "full_transparency" / f"{zoo}__{side}.json"
        path.write_text(json.dumps(game, indent=1) + "\n")
        u = game["uniform_starts"]
        print(f"wrote {path}: {len(game['equilibria'])} extreme equilibria, "
              f"{u['n_converged']} of {u['n']} uniform starts converged")
    for sweep in PARTIAL_TRANSPARENCY_SWEEPS:
        games = partial_transparency_sweep(args.source / "egt_fine" / sweep)
        path = args.out / "partial_transparency" / f"{sweep}.json"
        path.write_text("[\n" + ",\n".join(json.dumps(g) for g in games) + "\n]\n")
        points = sum(len(g["grid_points"]) for g in games)
        print(f"wrote {path}: {len(games)} distinct games, {points} grid points, "
              f"{sum('cycle' in g for g in games)} where populations cycle")


if __name__ == "__main__":
    main()

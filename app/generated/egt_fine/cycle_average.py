"""Long-run time-averaged Pr[(C,C)] in the games where the replicator dynamics cycle (behavioral, floor side).

Run from `app/`, after run_fine.sh:  uv run python generated/egt_fine/cycle_average.py
For every run whose replicator stage left starts unconverged, integrates 40 interior starts to t = 30,000 and
averages Pr[(C,C)] over [10,000, 30,000]. Writes behavioral_engine_side/cycling_time_averages.json, which
latex/scripts/gen_partial_transparency_figs.py reads for the "cycles" segments.
"""
import glob
import json

import numpy as np
from scipy.integrate import solve_ivp

from pd_runner.egt.faces.io import load_numeric_matrix
from pd_runner.egt.replicator.dynamics import growth_rates, simplex_samples, softmax

ROOT = "generated/egt_fine/behavioral_engine_side"
N_STARTS, SEED = 40, 20260514
T_BURN, T_END = 10_000, 30_000

out = {}
for path in sorted(glob.glob(f"{ROOT}/runs/*/replicator/basins.json")):
    with open(path) as fh:
        basins = json.load(fh)
    if not basins["n_unconverged"]:
        continue
    run_dir = path.rsplit("/", 2)[0]
    run = run_dir.rsplit("/", 1)[1]
    with open(f"{run_dir}/summary.json") as fh:
        summary = json.load(fh)
    names, A = load_numeric_matrix(f"{run_dir}/ess/payoff_matrix_numeric.csv")
    names, A = list(names), np.asarray(A, float)
    CC = (A == 2.0).astype(float)   # R = 2 is the payoff of (C, C) only

    def field(_, z, A=A):
        return growth_rates(A, softmax(z))

    avgs, support = [], set()
    for x0 in simplex_samples(len(names), N_STARTS, SEED, include_vertices=False, include_uniform=False):
        sol = solve_ivp(field, (0, T_END), np.log(x0), method="LSODA",
                        t_eval=np.linspace(T_BURN, T_END, 8001), rtol=1e-9, atol=1e-11)
        X = np.array([softmax(z) for z in sol.y.T])
        avgs.append(float(np.mean(np.einsum("ti,ij,tj->t", X, CC, X))))
        support |= {names[i] for i in np.flatnonzero(X.mean(axis=0) > 1e-3)}
    points = sorted(tuple(p) for p in summary["grid_points"])
    out[run] = {
        "grid_points": points, "time_avg_coop_mean": float(np.mean(avgs)),
        "min": float(min(avgs)), "max": float(max(avgs)), "support": sorted(support),
        "n_unconverged": basins["n_unconverged"], "n": basins["n_interior_samples"],
    }
    print(run, points, f"time-avg Pr[CC] mean {np.mean(avgs):.3f} ({min(avgs):.3f} to {max(avgs):.3f})",
          "cycling on", sorted(support), f"unconverged {basins['n_unconverged']}/{basins['n_interior_samples']}")
with open(f"{ROOT}/cycling_time_averages.json", "w") as fh:
    json.dump(out, fh, indent=1)

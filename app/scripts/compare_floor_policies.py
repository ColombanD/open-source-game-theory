"""Side-by-side of the engine-side and hinge-side sweeps of one zoo (both σ families).

    uv run python scripts/compare_floor_policies.py <zoo> [family ...]

Prints, per family: the stochastically-stable-set grid (M=100, β=1) under both floor
policies, DupocBot's stationary share grid under both, and the grid points where the
SS set differs. Reads `analysis`-style tidy tables via `egt.analysis.load_tidy`.
"""
import json, sys
from pathlib import Path
import pandas as pd
from pd_runner.egt.analysis import load_tidy, _grid
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

pd.set_option("display.width", 250)
zoo = sys.argv[1]
families = sys.argv[2:] or ["behavioral", "syntactic"]
eng = load_tidy(); hin = load_tidy(floor_policy="hinge_side")

def dup_share(run_dir, M=100, beta=1.0):
    mo = json.load(open(Path(run_dir) / "moran/stationary.json"))
    for p in mo["points"]:
        if p["population"] == M and p["beta"] == beta:
            return round(dict(p["stationary"]).get("DupocBot", 0.0), 3)

for fam in families:
    e = eng[(eng.zoo == zoo) & (eng.family == fam)]; g = hin[(hin.zoo == zoo) & (hin.family == fam)]
    print(f"\n##### {zoo} / {fam}: rows engine {len(e)} hinge {len(g)}")
    if len(e) < 36 or len(g) < 36:
        print("   (incomplete sweep)"); continue
    print("-- stochastically stable set (M=100, β=1): engine | hinge")
    print(pd.concat({"engine": _grid(e[e.alpha > 0], "moran_ss"), "hinge": _grid(g[g.alpha > 0], "moran_ss")}, axis=1).to_string())
    print("-- DupocBot share at (100,1): engine | hinge")
    for df, lab in ((e, "engine"), (g, "hinge")):
        d = df[df.alpha > 0].copy(); d["dup"] = [dup_share(DEFAULT_OUT_ROOT / "runs" / r) for r in d.run]
        print(lab); print(_grid(d, "dup").to_string())
    m = e.merge(g, on=["zoo", "family", "t", "alpha"], suffixes=("_e", "_h"))
    d = m[(m.moran_ss_e != m.moran_ss_h) | (m.dominant_support_e != m.dominant_support_h)]
    print(f"-- {len(d)}/{len(m)} grid points differ (SS set differs at {(m.moran_ss_e != m.moran_ss_h).sum()})")
    print(d[d.moran_ss_e != d.moran_ss_h][["t", "alpha", "moran_ss_e", "moran_ss_h"]].to_string(index=False))

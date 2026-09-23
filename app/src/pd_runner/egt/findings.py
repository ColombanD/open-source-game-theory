"""Step 3 of the paper analysis: CLAIM-DRIVEN findings over the flattened sweeps.

Where `analysis.py` flattens (step 2), this module answers the paper's questions,
drilling into the per-run `moran/stationary.json` for the full (M, β) sweep so
no claim rests on the single M=100, β=1 headline. Sections of
`<out_root>/analysis/findings.md`:

1. **Baseline (§5.1)** — the body zoo's t=1 anchor cell: stage headlines and the
   full (M, β) Moran table (the "rises with selection intensity" trajectory).
2. **Critical transparency (§5.2)** — per (zoo, family, α): how far down the
   t-axis the t=1 stochastically-stable set survives, and what replaces it.
3. **Selection robustness** — per grid point: how many of the 9 (M, β) combos
   agree with the headline SS set. A claim quoted from the headline should come
   from a region that is robust here, or be stated as selection-dependent.
4. **Aggregator ablation (body+twins+natives, epsilon)** — stationary SHARES of the
   Löbian class members (Dup/CIM/Max/Min) per (t, α) at strong selection, and
   the {Max, Min} drop-out order along t. The four are payoff-identical at
   point mass (neutral — shares split), so the CLASS total matters at t=1 and
   the individual shares only become meaningful under blur.
5. **Zoo sensitivity (§5.1.3 / appendix)** — body vs body+twins (behavioral):
   where the winners change, and whether CIMCIC splits the Löbian niche
   (mixed {Dup, CIM} dominant supports).
6. **The Max band (body+twins+natives, behavioral)** — cells where MaxConfidence is
   UNIQUELY stochastically stable, for comparison with the archived pre-freeze
   observation (TAUBOTS.md §4; then `default+confidence`, t ∈ [0.2, 0.6],
   α ≥ 0.45). This is the ambiguity-aversion-under-twinning result, NOT part
   of the ablation (the behavioral family confounds aggregator with twinning).

Run with `uv run python -m pd_runner.egt.findings`. α = 0 rows are excluded
everywhere (degenerate unconditional cooperation).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pandas as pd

from pd_runner.egt.analysis import _grid, _short, load_tidy
from pd_runner.egt.integrity import load_run_summaries
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

LOEBIAN = ("DupocBot", "CIMCIC", "MaxConfidenceBot", "MinConfidenceBot")


def _fence(obj) -> str:
    return "```\n" + (obj if isinstance(obj, str) else obj.to_string()) + "\n```\n"


def _moran_points(run_dir: Path) -> list[dict]:
    f = run_dir / "moran" / "stationary.json"
    return json.loads(f.read_text())["points"] if f.exists() else []


def load_moran(out_root: Path) -> pd.DataFrame:
    """One row per (zoo, family, t, α, M, β): SS set + stationary share dict."""
    rows = []
    for r in load_run_summaries(out_root):
        for p in _moran_points(r["_dir"]):
            base = {
                "zoo": r["zoo"], "family": r["family"],
                "population": p["population"], "beta": p["beta"],
                "converged": p["converged"],
                "ss": _short(p["stochastically_stable"]),
                "shares": dict(p["stationary"]),
            }
            for t, alpha in r["grid_points"]:
                rows.append({"t": t, "alpha": alpha, **base})
    return pd.DataFrame(rows)


# ── 1. Baseline ───────────────────────────────────────────────────────────────


def baseline(tidy: pd.DataFrame, moran: pd.DataFrame) -> str:
    cell = tidy[(tidy.zoo == "body") & (tidy.family == "behavioral")
                & (tidy.t == 1.0) & (tidy.alpha == 0.3)].iloc[0]
    out = ["## 1. Baseline — body zoo, t = 1 (the anchor matrix = the base matrix)\n",
           f"pure ESS: {cell.n_pure_ess} · extreme NE: {cell.n_extreme_ne} in "
           f"{cell.n_ne_components} components · invasion SCCs: {cell.n_sccs} · "
           f"stable faces: {cell.n_stable_faces}/{cell.n_supports} supports\n",
           f"dominant replicator support: {cell.dominant_support} "
           f"(basin {cell.largest_basin:.0%})\n",
           "Full (M, β) Moran table (DupocBot share of the stationary distribution):\n"]
    m = moran[(moran.zoo == "body") & (moran.family == "behavioral")
              & (moran.t == 1.0) & (moran.alpha == 0.3)]
    tab = m.assign(dup=[s.get("DupocBot", 0.0) for s in m.shares]).pivot_table(
        index="population", columns="beta", values="dup")
    out.append(_fence(tab.map(lambda v: f"{v:.0%}")))
    ss = m.pivot_table(index="population", columns="beta", values="ss", aggfunc="first")
    out.append("Stochastically stable set per (M, β):\n")
    out.append(_fence(ss))
    return "\n".join(out)


# ── 2. Critical transparency ─────────────────────────────────────────────────


def critical_transparency(tidy: pd.DataFrame) -> str:
    out = ["## 2. Critical transparency — how far down t the t=1 winners survive\n",
           "Per α: the M=100/β=1 SS set along t (1.0 → 0.0); `t*` = first t where "
           "it departs from the t=1 set.\n"]
    for (zoo, family), g in tidy[tidy.alpha > 0].groupby(["zoo", "family"]):
        lines = []
        for alpha, ga in g.groupby("alpha"):
            path = ga.sort_values("t", ascending=False)[["t", "moran_ss"]]
            ref = path.iloc[0].moran_ss
            changed = path[path.moran_ss != ref]
            tstar = f"t*={changed.iloc[0].t:g}→{changed.iloc[0].moran_ss}" \
                if len(changed) else "stable on the whole grid"
            seq = "  ".join(f"{r.t:g}:{r.moran_ss}" for r in path.itertuples())
            lines.append(f"α={alpha:<5g} [{tstar}]  {seq}")
        out.append(f"### {zoo} — {family}\n")
        out.append(_fence("\n".join(lines)))
    return "\n".join(out)


# ── 3. Selection robustness ──────────────────────────────────────────────────


def robustness(moran: pd.DataFrame) -> str:
    out = ["## 3. Selection robustness — # of the 9 (M, β) combos whose SS set "
           "equals the M=100/β=1 headline\n",
           "9 = fully robust; low values mean the headline is a strong-selection "
           "statement (weak selection usually clears no stochastic-stability "
           "cut at all, which depresses these counts honestly).\n"]
    for (zoo, family), g in moran[moran.alpha > 0].groupby(["zoo", "family"]):
        def agree(cell: pd.DataFrame) -> int:
            head = cell[(cell.population == 100) & (cell.beta == 1.0)].ss.iloc[0]
            return int((cell.ss == head).sum())
        counts = (g.groupby(["alpha", "t"])[["population", "beta", "ss"]]
                  .apply(agree).rename("n").reset_index())
        grid = counts.pivot_table(index="alpha", columns="t", values="n") \
            .sort_index().sort_index(axis=1, ascending=False)
        out.append(f"### {zoo} — {family}\n")
        out.append(_fence(grid))
    return "\n".join(out)


# ── 4. Aggregator ablation shares ────────────────────────────────────────────


def ablation(moran: pd.DataFrame) -> str:
    g = moran[(moran.zoo == "body+twins+natives") & (moran.family == "epsilon")
              & (moran.population == 100) & (moran.beta == 1.0)
              & (moran.alpha > 0)]
    if g.empty:
        return "## 4. Aggregator ablation — no body+twins+natives/epsilon runs found\n"
    out = ["## 4. Aggregator ablation — body+twins+natives on epsilon, "
           "stationary shares at M=100, β=1\n",
           "Columns: the three aggregators over Dupoc's test (sum = the Dup+CIM "
           "lifts, payoff-twins at t=1) and the Löbian class total.\n"]
    rows = []
    for r in g.sort_values(["alpha", "t"], ascending=[True, False]).itertuples():
        s = r.shares
        rows.append({
            "alpha": r.alpha, "t": r.t,
            "sum(Dup+CIM)": s.get("DupocBot", 0) + s.get("CIMCIC", 0),
            "max(Max)": s.get("MaxConfidenceBot", 0.0),
            "min(Min)": s.get("MinConfidenceBot", 0.0),
            "class total": sum(s.get(b, 0.0) for b in LOEBIAN),
            "SS": r.ss,
        })
    tab = pd.DataFrame(rows)
    for c in ("sum(Dup+CIM)", "max(Max)", "min(Min)", "class total"):
        tab[c] = tab[c].map(lambda v: f"{v:.0%}")
    out.append(_fence(tab.to_string(index=False)))
    return "\n".join(out)


# ── 5. Zoo sensitivity ───────────────────────────────────────────────────────


def zoo_sensitivity(tidy: pd.DataFrame) -> str:
    a = tidy[(tidy.zoo == "body") & (tidy.family == "behavioral") & (tidy.alpha > 0)]
    b = tidy[(tidy.zoo == "body+twins") & (tidy.family == "behavioral")
             & (tidy.alpha > 0)]
    m = pd.merge(a, b, on=["t", "alpha"], suffixes=("_body", "_twins"))
    diff = m[m.moran_ss_body != m.moran_ss_twins]
    mixed = b[b.dominant_support.str.contains("CIM")
              & b.dominant_support.str.contains("Dup")]
    out = ["## 5. Zoo sensitivity — body vs body+twins (behavioral)\n",
           f"SS set changes at {len(diff)}/{len(m)} grid points; "
           f"{len(mixed)}/{len(b)} twins-zoo points have a dominant support "
           "mixing Dup and CIM (the Löbian niche splitting across the twin pair).\n"]
    if len(diff):
        out.append(_fence(diff.sort_values(["t", "alpha"], ascending=[False, True])
                          [["t", "alpha", "moran_ss_body", "moran_ss_twins"]]
                          .to_string(index=False)))
    return "\n".join(out)


# ── 6. The Max band ──────────────────────────────────────────────────────────


def max_band(tidy: pd.DataFrame) -> str:
    g = tidy[(tidy.zoo == "body+twins+natives") & (tidy.family == "behavioral")
             & (tidy.alpha > 0)]
    band = g[g.moran_ss == "Max"]
    out = ["## 6. The Max band — body+twins+natives on BEHAVIORAL (twinning, not ablation)\n",
           "Cells where MaxConfidence is UNIQUELY stochastically stable at "
           "M=100/β=1. Archived pre-freeze observation (10-member zoo): "
           "t ∈ [0.2, 0.6] at α ≥ 0.45.\n"]
    if len(band):
        out.append(_fence(band.sort_values(["alpha", "t"])[["t", "alpha"]]
                          .to_string(index=False)))
    else:
        out.append("No such cells on the 14-bot roster — the band did not "
                   "reproduce; report the change.\n")
    out.append("Full SS map for context:\n")
    out.append(_fence(_grid(g, "moran_ss")))
    return "\n".join(out)


def main() -> int:
    out_root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT_ROOT
    tidy = load_tidy(out_root)
    moran = load_moran(out_root)
    sections = [
        "# Findings — claim-driven analysis over the frozen sweeps\n",
        baseline(tidy, moran),
        critical_transparency(tidy),
        robustness(moran),
        ablation(moran),
        zoo_sensitivity(tidy),
        max_band(tidy),
    ]
    dest = out_root / "analysis" / "findings.md"
    dest.write_text("\n\n".join(sections))
    print(f"findings -> {dest}")
    nonconv = moran[~moran.converged]
    if len(nonconv):
        print(f"WARNING: {len(nonconv)} non-converged Moran points excluded from "
              "nothing — check before citing affected cells")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

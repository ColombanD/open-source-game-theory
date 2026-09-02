"""Step 4 of the paper analysis: the STATIC COLLAPSE — Nash structure over t.

The dynamic stages say where a population goes; this module tracks what happens
to the space of RATIONAL CONVENTIONS itself as transparency falls. Component
COUNTS alone can mislead (a count can stay constant while its content changes;
extreme-NE vertex counts are polytope geometry, not strategy content), so each
Nash component is CLASSIFIED by the best cooperation rate among its equilibria —
read from `nash/latest/equilibria.jsonl`, which carries `cooperation_rate_float`
and `component_id` per extreme NE.

Per (zoo, family, t, α) it computes:

* `max_ne_coop`       — the STATIC CEILING: the best cooperation rate any Nash
                        equilibrium supports at all;
* `n_coop_components` — components whose best equilibrium cooperates ≥ ½;
* `full_coop_exists`  — is a fully-cooperative component still in the landscape?
* joined from the other stages: `n_ne_components`, `n_stable_faces`, and the
  REALIZED cooperation rate of the Moran stationary distribution (M=100, β=1):
  the share-weighted self-play cooperation of the population — under small
  mutation the stationary mass sits on monocultures, so this is Σ share(i) ·
  [i's self-cell is mutual C], read off the payoff diagonal (b−c vs 0). NOT the
  Löbian-class SHARE: at low t the Löbian types survive as DEFECTORS, and a
  share curve would conflate identity with cooperation (it visibly exceeded the
  static ceiling — the tell that caught it).

Outputs under `<out_root>/analysis/`: `nash_structure.csv` (the table view),
`nash_structure.md` (pivots + the static-vs-dynamic collapse comparison), and
one figure per sweep, `fig_collapse_<zoo>_<family>.png` — small multiples over
α, two rows (cooperation on [0,1]; equilibrium-structure counts), never a dual
axis. The t* marker is the Moran collapse (first departure of the M=100/β=1
SS set from its t=1 value, walking t downward; α = 0 excluded as always).

Run with `uv run python -m pd_runner.egt.nash_structure`.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import pandas as pd

from pd_runner.egt.analysis import load_tidy
from pd_runner.egt.findings import load_moran
from pd_runner.egt.integrity import load_run_summaries
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

# The repo's Okabe-Ito order (tau/report.py, egt/report.py — validated there with
# the dataviz palette checker; its contrast WARN is why every figure ships direct
# labels/legend AND the CSV table view). Blue = cooperation across the project.
C_STATIC, C_REALIZED, C_COMPONENTS, C_FACES = "#0072b2", "#e69f00", "#d55e00", "#009e73"
C_MARKER = "#8c8c96"


def _latest_nash(run_dir: Path) -> Path | None:
    latest = run_dir / "nash" / "latest"
    if (latest / "equilibria.jsonl").exists():
        return latest
    candidates = sorted(d for d in (run_dir / "nash" / "runs").glob("*")
                        if (d / "equilibria.jsonl").exists())
    return candidates[-1] if candidates else None


def _self_coop(run_dir: Path) -> dict[str, int]:
    """bot → 1 iff its SELF-PLAY cell at this (t, α) is mutual cooperation.

    The payoff diagonal is b−c (> 0) for (C, C) and 0 for (D, D) — self-play is
    symmetric, so no other value occurs there."""
    f = run_dir / "ess" / "payoff_matrix_numeric.csv"
    if not f.exists():
        return {}
    m = pd.read_csv(f, index_col=0)
    return {b: int(m.loc[b, b] > 0) for b in m.index}


def load_nash_structure(out_root: Path = DEFAULT_OUT_ROOT) -> pd.DataFrame:
    """One row per grid point: component-level cooperation classification."""
    rows = []
    for r in load_run_summaries(out_root):
        nash_dir = _latest_nash(r["_dir"])
        if nash_dir is None:
            continue
        eqs = [json.loads(line) for line in
               (nash_dir / "equilibria.jsonl").read_text().splitlines()]
        by_comp: dict[int, float] = {}
        for e in eqs:
            c = e["component_id"]
            by_comp[c] = max(by_comp.get(c, 0.0), e["cooperation_rate_float"])
        diag = _self_coop(r["_dir"])
        base = {
            "zoo": r["zoo"], "family": r["family"], "fingerprint": r["fingerprint"],
            "selfcoop": diag,
            "n_ne": len(eqs),
            "n_components": len(by_comp),
            "max_ne_coop": max(by_comp.values(), default=0.0),
            "n_coop_components": sum(1 for v in by_comp.values() if v >= 0.5),
            "full_coop_exists": any(v >= 0.999 for v in by_comp.values()),
        }
        for t, alpha in r["grid_points"]:
            rows.append({"t": t, "alpha": alpha, **base})
    return pd.DataFrame(rows)


def _assemble(out_root: Path) -> pd.DataFrame:
    """Join the static classification with faces + the realized Moran share."""
    ns = load_nash_structure(out_root)
    tidy = load_tidy(out_root)[
        ["zoo", "family", "t", "alpha", "n_stable_faces", "moran_ss"]]
    moran = load_moran(out_root)
    strong = moran[(moran.population == 100) & (moran.beta == 1.0)]
    df = ns.merge(tidy, on=["zoo", "family", "t", "alpha"]).merge(
        strong[["zoo", "family", "t", "alpha", "shares"]],
        on=["zoo", "family", "t", "alpha"])
    df["realized_coop"] = [
        sum(share * row.selfcoop.get(bot, 0) for bot, share in row.shares.items())
        for row in df.itertuples()]
    return (df.drop(columns=["shares", "selfcoop"])
            .sort_values(["zoo", "family", "alpha", "t"]).reset_index(drop=True))


def _tstar(g: pd.DataFrame) -> float | None:
    """Moran collapse for one (zoo, family, α): first t below 1.0 whose SS set
    departs from the t=1 set (None if stable across the grid)."""
    path = g.sort_values("t", ascending=False)
    ref = path.iloc[0].moran_ss
    changed = path[path.moran_ss != ref]
    return float(changed.iloc[0].t) if len(changed) else None


def collapse_table(df: pd.DataFrame) -> pd.DataFrame:
    """Static vs dynamic collapse per (zoo, family, α): the t at which the
    fully-cooperative component leaves the landscape vs the Moran t*."""
    rows = []
    for (zoo, family, alpha), g in df[df.alpha > 0].groupby(
            ["zoo", "family", "alpha"]):
        path = g.sort_values("t", ascending=False)
        lost = path[~path.full_coop_exists]
        rows.append({
            "zoo": zoo, "family": family, "alpha": alpha,
            "t_static": float(lost.iloc[0].t) if len(lost) else None,
            "t_moran": _tstar(g),
        })
    return pd.DataFrame(rows)


def figure(df: pd.DataFrame, zoo: str, family: str, dest: Path) -> None:
    g = df[(df.zoo == zoo) & (df.family == family) & (df.alpha > 0)]
    alphas = sorted(g.alpha.unique())
    fig, axes = plt.subplots(2, len(alphas), figsize=(3.0 * len(alphas), 5.4),
                             sharex=True, sharey="row")
    for j, alpha in enumerate(alphas):
        ga = g[g.alpha == alpha].sort_values("t")
        ts = _tstar(ga)
        top, bot = axes[0][j], axes[1][j]
        top.plot(ga.t, ga.max_ne_coop, color=C_STATIC, lw=2,
                 label="static ceiling (best NE coop rate)")
        top.plot(ga.t, ga.realized_coop, color=C_REALIZED, lw=2, ls="--",
                 label="realized (stationary coop rate, M=100 β=1)")
        bot.plot(ga.t, ga.n_components, color=C_COMPONENTS, lw=2,
                 drawstyle="steps-mid", label="NE components")
        bot.plot(ga.t, ga.n_coop_components, color=C_COMPONENTS, lw=2, ls=":",
                 drawstyle="steps-mid", label="…cooperative (≥½)")
        bot.plot(ga.t, ga.n_stable_faces, color=C_FACES, lw=2, ls="--",
                 drawstyle="steps-mid", label="stable faces")
        for ax in (top, bot):
            if ts is not None:
                ax.axvline(ts, color=C_MARKER, lw=1.2, ls="--")
            ax.grid(True, alpha=0.25, lw=0.5)
            ax.spines[["top", "right"]].set_visible(False)
        if ts is not None:
            top.annotate("Moran t*", (ts, 1.02), color=C_MARKER, fontsize=8,
                         ha="center", annotation_clip=False)
        top.set_title(f"α = {alpha:g}", fontsize=10)
        top.set_ylim(-0.03, 1.05)
        bot.set_xlabel("transparency t")
        bot.set_xlim(-0.02, 1.02)
    axes[0][0].set_ylabel("cooperation rate")
    axes[1][0].set_ylabel("count")
    axes[0][0].legend(fontsize=8, loc="lower right", frameon=False)
    axes[1][0].legend(fontsize=8, loc="upper left", frameon=False)
    fig.suptitle(f"Static vs dynamic collapse — {zoo} / {family}", fontsize=12)
    fig.tight_layout()
    fig.savefig(dest, dpi=180)
    plt.close(fig)


def report(df: pd.DataFrame, coll: pd.DataFrame) -> str:
    out = ["# Nash structure over transparency — the static collapse\n",
           "`max_ne_coop` = best cooperation rate any extreme NE supports (the "
           "static ceiling); a 'cooperative component' has a member ≥ ½.\n"]
    for (zoo, family), g in df[df.alpha > 0].groupby(["zoo", "family"]):
        out.append(f"## {zoo} — {family}\n")
        for col, title in (("max_ne_coop", "static ceiling"),
                           ("n_coop_components", "cooperative components"),
                           ("n_components", "NE components")):
            p = g.pivot_table(index="alpha", columns="t", values=col) \
                .sort_index().sort_index(axis=1, ascending=False)
            out.append(f"### {title}\n```\n{p.round(2).to_string()}\n```\n")
        c = coll[(coll.zoo == zoo) & (coll.family == family)]
        out.append("### collapse points (t_static = full-coop component gone; "
                   "t_moran = SS set departs its t=1 value)\n"
                   f"```\n{c[['alpha', 't_static', 't_moran']].to_string(index=False)}\n```\n")
    return "\n".join(out)


def main() -> int:
    out_root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT_ROOT
    df = _assemble(out_root)
    coll = collapse_table(df)
    dest = out_root / "analysis"
    dest.mkdir(parents=True, exist_ok=True)
    df.to_csv(dest / "nash_structure.csv", index=False)
    (dest / "nash_structure.md").write_text(report(df, coll))
    for (zoo, family), _ in df.groupby(["zoo", "family"]):
        fig_path = dest / f"fig_collapse_{zoo.replace('+', '_')}_{family}.png"
        figure(df, zoo, family, fig_path)
        print(f"figure -> {fig_path}")
    print(f"table  -> {dest / 'nash_structure.csv'}")
    print(f"report -> {dest / 'nash_structure.md'}\n")
    body = coll[(coll.zoo == "body") & (coll.family == "behavioral")]
    print("body/behavioral collapse points:\n",
          body[["alpha", "t_static", "t_moran"]].to_string(index=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

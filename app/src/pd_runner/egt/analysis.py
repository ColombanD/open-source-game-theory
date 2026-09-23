"""Step 2 of the paper analysis: FLATTEN the sweep artefacts into one tidy table.

The sweep writes one directory per distinct matrix; the analysis plane is one row
per (zoo, family, t, α) GRID POINT — the dedup is undone via each run's
`grid_points`, so deduped points reappear as rows sharing a fingerprint. Like
`integrity.py`, this reads only `runs/*/summary.json` (complete, self-describing;
the top-level `sweep_summary*.json` files are clobbered across zoos).

Outputs, under `<out_root>/analysis/`:

* `tidy.csv` — the dataset. One row per grid point with the headline metric of
  every stage: pure-ESS count; invasion edges/SCCs/cycles; face-class counts
  (stable faces = the `asymp_stable*` classes); extreme NE + components;
  replicator attractors, largest basin + dominant support; the Moran headline
  (strongest selection, M=100 β=1) stochastically-stable set. Descriptive
  coop-rate statistics are deliberately NOT here — they are the tau layer's
  (`tau/stats.py`), computed over tournaments, not over run artefacts.
* `phase_maps.md` — per (zoo, family): the t×α grid rendered twice, colored by
  the stochastically-stable set and by the dominant replicator support. Cells
  that share a fingerprint are provably identical, so equal neighbours ARE the
  phase regions ("report per phase region, not per grid point").
* `family_diffs.md` — per zoo with two families: the grid points where the two
  σ families disagree on either headline, i.e. where the confusion STRUCTURE
  (not the information rate — t is matched) changes the evolutionary outcome.

Run with `uv run python -m pd_runner.egt.analysis`. The α = 0 column is the
degenerate unconditional-cooperation regime (`≥ α` at α = 0 always fires) — keep
it in the table, exclude it from base-matrix comparisons.
"""

from __future__ import annotations

import sys
from pathlib import Path

import pandas as pd

from pd_runner.egt.integrity import load_run_summaries
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

# Short display names for grid cells. Anything not listed keeps its full name.
ABBREV: dict[str, str] = {
    "CooperateBot": "Coop", "DefectBot": "Def", "TitForTatBot": "TFT",
    "DupocBot": "Dup", "CupodBot": "Cup", "CupodTrollBot": "CupT",
    "DBot": "DB", "EBot": "EB", "OBot": "OB", "DIMCID": "DIM", "CIMCIC": "CIM",
    "PrudentBot": "Pru", "MaxConfidenceBot": "Max", "MinConfidenceBot": "Min",
    "MirrorBot": "Mir", "GuardianBot": "Guar", "JustBot": "Just",
}


def _short(bots: list[str]) -> str:
    """A stable, compact label for a set/support of bots ('—' for empty)."""
    return "+".join(ABBREV.get(b, b) for b in sorted(bots)) if bots else "—"


def load_tidy(out_root: Path = DEFAULT_OUT_ROOT) -> pd.DataFrame:
    """One row per (zoo, family, t, α) grid point, headline metrics flattened."""
    rows: list[dict] = []
    for r in load_run_summaries(out_root):
        st = r.get("stages") or {}
        faces_by_class = (st.get("faces") or {}).get("by_class") or {}
        moran_head = (st.get("moran") or {}).get("headline") or {}
        base = {
            "zoo": r["zoo"],
            "family": r["family"],
            "fingerprint": r["fingerprint"],
            "run": r["run"],
            "n_types": r.get("n_types"),
            "is_fully_proven": r.get("is_fully_proven"),
            "n_pure_ess": (st.get("ess") or {}).get("n_pure_ess"),
            "edges_strict": (st.get("invasion") or {}).get("edges_strict"),
            "n_sccs": (st.get("invasion") or {}).get("n_sccs"),
            "n_cycles": (st.get("invasion") or {}).get("n_cycles"),
            "n_supports": (st.get("faces") or {}).get("n_supports"),
            "n_stable_faces": sum(
                v for k, v in faces_by_class.items() if k.startswith("asymp_stable")),
            "n_extreme_ne": (st.get("nash") or {}).get("n_extreme_NE"),
            "n_ne_components": (st.get("nash") or {}).get("n_components"),
            "n_attractors": (st.get("replicator") or {}).get("n_attractors"),
            "largest_basin": (st.get("replicator") or {}).get("largest_basin"),
            "dominant_support": _short(
                (st.get("replicator") or {}).get("dominant_support") or []),
            "moran_ss": _short(moran_head.get("stochastically_stable") or []),
            "moran_population": moran_head.get("population"),
            "moran_beta": moran_head.get("beta"),
        }
        for t, alpha in r["grid_points"]:
            rows.append({"t": t, "alpha": alpha, **base})
    df = pd.DataFrame(rows).sort_values(
        ["zoo", "family", "t", "alpha"], ascending=[True, True, False, True])
    return df.reset_index(drop=True)


def _grid(df: pd.DataFrame, value: str) -> pd.DataFrame:
    """α (rows, ascending) × t (columns, 1.0 first) pivot of one label column."""
    p = df.pivot_table(index="alpha", columns="t", values=value, aggfunc="first")
    return p.sort_index().sort_index(axis=1, ascending=False)


def phase_maps(df: pd.DataFrame) -> str:
    """The t×α grids per (zoo, family), for the two headline views."""
    out: list[str] = ["# Phase maps — cells sharing a value form the phase regions",
                      "", "α=0 row: degenerate unconditional cooperation (`≥ α`).", ""]
    for (zoo, family), g in df.groupby(["zoo", "family"], sort=True):
        out.append(f"## {zoo} — {family}")
        for value, title in (("moran_ss", "stochastically stable (M=100, β=1)"),
                             ("dominant_support", "dominant replicator support")):
            out.append(f"\n### {title}\n")
            out.append("```\n" + _grid(g, value).to_string() + "\n```\n")
    return "\n".join(out)


def family_diffs(df: pd.DataFrame) -> str:
    """Grid points where two σ families of one zoo disagree on a headline —
    the evolutionary footprint of confusion STRUCTURE at matched information."""
    out: list[str] = ["# Cross-family disagreements (same zoo, same (t, α))", ""]
    for zoo, g in df.groupby("zoo", sort=True):
        fams = sorted(g["family"].unique())
        if len(fams) < 2:
            continue
        a, b = fams[:2]
        merged = pd.merge(
            g[g["family"] == a], g[g["family"] == b],
            on=["zoo", "t", "alpha"], suffixes=(f"_{a}", f"_{b}"))
        diff = merged[
            (merged[f"moran_ss_{a}"] != merged[f"moran_ss_{b}"])
            | (merged[f"dominant_support_{a}"] != merged[f"dominant_support_{b}"])]
        out.append(f"## {zoo}: {a} vs {b} — {len(diff)}/{len(merged)} points differ\n")
        if len(diff):
            cols = ["t", "alpha",
                    f"moran_ss_{a}", f"moran_ss_{b}",
                    f"dominant_support_{a}", f"dominant_support_{b}"]
            out.append("```\n" + diff.sort_values(
                ["t", "alpha"], ascending=[False, True])[cols]
                .to_string(index=False) + "\n```")
        out.append("")
    return "\n".join(out)


def main() -> int:
    out_root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT_ROOT
    df = load_tidy(out_root)
    dest = out_root / "analysis"
    dest.mkdir(parents=True, exist_ok=True)

    df.to_csv(dest / "tidy.csv", index=False)
    (dest / "phase_maps.md").write_text(phase_maps(df))
    (dest / "family_diffs.md").write_text(family_diffs(df))

    print(f"tidy table: {len(df)} grid-point rows, "
          f"{df['fingerprint'].nunique()} distinct matrices, "
          f"{df.groupby(['zoo', 'family']).ngroups} sweeps -> {dest / 'tidy.csv'}")
    print(f"phase maps -> {dest / 'phase_maps.md'}")
    print(f"family diffs -> {dest / 'family_diffs.md'}\n")

    # A taste of the dataset: the mainline zoo's stochastic-stability map.
    body = df[(df.zoo == "body") & (df.family == "behavioral")]
    if len(body):
        print("body / behavioral — stochastically stable (M=100, β=1):")
        print(_grid(body, "moran_ss").to_string())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

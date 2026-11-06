"""Figure versions of the three (t, α)-grid tables of the transparency section, body8, PA-S', engine side,
with BOTH distance channels in one plot (behavioral = the reference, syntactic = the overlay):

  fig_tau_fullcoop_grid   does a fully cooperative Nash component exist? cell colour = under both channels /
                          behavioral only / syntactic only / neither
  fig_tau_phase_grid      the stochastically stable set at (M, β) = (100, 1), behavioral in each cell;
                          where the syntactic set differs it is written below in italics and the cell is hatched
  fig_tau_ladder          critical transparency t_c(α) per zoo rung (behavioral, solid); body8 under the
                          syntactic channel dotted

Run from `app/`:  uv run python ../latex/scripts/gen_tau_grid_figs.py
Inputs: app/generated/egt/analysis/nash_structure.csv (body8, both families) and the ladder run directories
(through gen_tau_ladder.load_points). Do not edit the outputs by hand.
"""
from __future__ import annotations

import sys
from pathlib import Path

import matplotlib
import pandas as pd

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.lines import Line2D  # noqa: E402
from matplotlib.patches import Patch, Rectangle  # noqa: E402

sys.path.insert(0, str(Path(__file__).resolve().parent))
APP = Path(__file__).resolve().parents[2] / "app"
OUT_DIR = Path(__file__).resolve().parents[1] / "figures and tables"
ALPHAS = [0.2, 0.4, 0.5, 0.6, 0.8, 1.0]
TS = [1.0, 0.8, 0.6, 0.4, 0.2, 0.0]
C_BOTH, C_BEH, C_SYN, C_NONE = "#2e8b57", "#0072b2", "#e69f00", "white"
plt.rcParams.update({"font.size": 9, "axes.titlesize": 9, "legend.fontsize": 8, "xtick.labelsize": 8, "ytick.labelsize": 8})

ns = pd.read_csv(APP / "generated" / "egt" / "analysis" / "nash_structure.csv")
ns = ns[(ns.zoo == "body8") & (ns.alpha > 0)]
grid = {fam: {(float(r.alpha), float(r.t)): r for r in ns[ns.family == fam].itertuples()} for fam in ("behavioral", "syntactic")}
for fam in grid:
    missing = [(a, t) for a in ALPHAS for t in TS if (a, t) not in grid[fam]]
    assert not missing, (fam, missing)


def save(fig, name):
    fig.savefig(OUT_DIR / f"{name}.pdf", bbox_inches="tight")
    fig.savefig(OUT_DIR / f"{name}.preview.png", dpi=150, bbox_inches="tight")
    plt.close(fig)


def grid_axes(ax, title):
    ax.set_xlim(0, len(TS)); ax.set_ylim(len(ALPHAS), 0)
    ax.set_xticks([i + 0.5 for i in range(len(TS))]); ax.set_xticklabels([f"{t:g}" for t in TS])
    ax.set_yticks([i + 0.5 for i in range(len(ALPHAS))]); ax.set_yticklabels([f"{a:g}" for a in ALPHAS])
    ax.set_xlabel("transparency $t$"); ax.set_ylabel(r"caution $\alpha$")
    ax.set_title(title); ax.tick_params(length=0)
    for s in ax.spines.values():
        s.set_visible(False)


# ── 1. fully cooperative component, both channels in one grid ───────────────
fig, ax = plt.subplots(figsize=(3.6, 2.9))
for i, a in enumerate(ALPHAS):
    for j, t in enumerate(TS):
        b = bool(grid["behavioral"][(a, t)].full_coop_exists); s = bool(grid["syntactic"][(a, t)].full_coop_exists)
        color = C_BOTH if b and s else C_BEH if b else C_SYN if s else C_NONE
        ax.add_patch(Rectangle((j, i), 1, 1, facecolor=color, edgecolor="0.6", lw=0.6, alpha=0.9 if color != "white" else 1))
grid_axes(ax, "fully cooperative Nash component")
ax.legend(handles=[Patch(facecolor=C_BOTH, label="both channels"), Patch(facecolor=C_BEH, label="behavioral only"),
                   Patch(facecolor=C_SYN, label="syntactic only"), Patch(facecolor="white", edgecolor="0.6", label="neither")],
          loc="upper center", bbox_to_anchor=(0.5, -0.22), ncol=2, frameon=False)
save(fig, "fig_tau_fullcoop_grid")

# ── 2. stochastically stable set, behavioral with the syntactic set where it differs ──
def kind(ss: str) -> str:
    if ss in ("—", "---", "", "nan"): return "empty"
    parts = ss.split("+")
    return "dup-alone" if parts == ["Dup"] else "dup-shared" if "Dup" in parts else "no-dup"

FILL = {"dup-alone": "#2e8b57", "dup-shared": "#a8d8b9", "no-dup": "#d9d9d9", "empty": "white"}
fig, ax = plt.subplots(figsize=(4.6, 2.9))
n_diff = 0
for i, a in enumerate(ALPHAS):
    for j, t in enumerate(TS):
        b = str(grid["behavioral"][(a, t)].moran_ss); s = str(grid["syntactic"][(a, t)].moran_ss)
        b_txt = "—" if kind(b) == "empty" else b.replace("+", "+\n") if b.count("+") >= 2 else b
        ax.add_patch(Rectangle((j, i), 1, 1, facecolor=FILL[kind(b)], edgecolor="0.6", lw=0.6))
        if s != b:
            n_diff += 1
            ax.add_patch(Rectangle((j, i), 1, 1, facecolor="none", edgecolor=C_SYN, lw=1.6))
            ax.text(j + 0.5, i + 0.36, b_txt, ha="center", va="center", fontsize=6.5)
            ax.text(j + 0.5, i + 0.76, ("—" if kind(s) == "empty" else s), ha="center", va="center", fontsize=6, style="italic", color="#a35f00")
        else:
            ax.text(j + 0.5, i + 0.5, b_txt, ha="center", va="center", fontsize=6.5)
grid_axes(ax, r"stochastically stable set, $(M,\beta)=(100,1)$")
ax.legend(handles=[Patch(facecolor=FILL["dup-alone"], label="Dup alone"), Patch(facecolor=FILL["dup-shared"], label="Dup with others"),
                   Patch(facecolor=FILL["no-dup"], label="without Dup"), Patch(facecolor="white", edgecolor="0.6", label="no selection"),
                   Patch(facecolor="none", edgecolor=C_SYN, lw=1.6, label="syntactic differs (in italics)")],
          loc="upper center", bbox_to_anchor=(0.5, -0.22), ncol=3, frameon=False)
save(fig, "fig_tau_phase_grid")

# ── 3. the ladder: t_c(α) per rung, behavioral; body8 syntactic dotted ──────
from gen_tau_ladder import load_points, LADDER  # noqa: E402  (reads the run directories)

def tc_from(points, a):
    alive = [t for t in TS if points[(a, t)]["realized"] >= 0.5]
    return min(alive) if alive else None

fig, ax = plt.subplots(figsize=(3.8, 2.6))
x = list(range(len(ALPHAS)))
markers = ["s", "o", "^", "D"]
offsets = [-0.09, -0.03, 0.03, 0.09]  # rungs with identical t_c would otherwise draw on top of each other
for (key, n, label), m, dx in zip(LADDER, markers, offsets):
    pts = load_points(key)
    ys = [tc_from(pts, a) for a in ALPHAS]
    ax.plot([xi + dx for xi in x], [y if y is not None else float("nan") for y in ys], marker=m, ms=4, lw=1.3,
            label=f"{label.replace(chr(92)+'texttt', '').replace('{', '').replace('}', '')} ($N={n}$)")
syn = [min([t for t in TS if grid["syntactic"][(a, t)].realized_coop >= 0.5], default=None) for a in ALPHAS]
ax.plot(x, [y if y is not None else float("nan") for y in syn], ":", lw=1.4, color="0.25", label="body, syntactic channel")
ax.set_xticks(x); ax.set_xticklabels([f"{a:g}" for a in ALPHAS]); ax.set_xlabel(r"caution $\alpha$")
ax.set_yticks(TS); ax.set_ylim(-0.05, 1.05); ax.set_ylabel("critical transparency $t_c$")
ax.grid(alpha=0.25); ax.legend(loc="upper left", frameon=False, fontsize=7)
save(fig, "fig_tau_ladder")
print(f"wrote fig_tau_fullcoop_grid, fig_tau_phase_grid ({n_diff} cells where the syntactic set differs), fig_tau_ladder")

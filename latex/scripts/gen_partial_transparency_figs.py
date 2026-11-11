"""Generate the two partial-transparency figures of the experiments section from the fine-grid runs.

Run from `app/`:  uv run python ../latex/scripts/gen_partial_transparency_figs.py
Reads  app/generated/egt_fine/{behavioral,syntactic}_engine_side/runs/*  (run_fine.sh, 2026-11-11: body8, t step
0.01, negative side of the hinge, Nash + replicator, 1,000 starts) and `cycling_time_averages.json` (written by
`app/generated/egt_fine/cycle_average.py`: the long-run average of Pr[(C,C)] in the games where no population
settles).
Writes app/generated/egt_fine/figures/{figure_A,figure_D}.pdf (+ .png previews) and `figure_data.json`.
It does NOT write into `latex/figures and tables/`: copy the PDFs there (or to Overleaf) by hand.

figure_A  equilibrium cooperation and selection, behavioral family, averaged over the six caution levels
figure_D  (a) small multiples, one per caution level: the cooperation the replicator dynamics select against
              transparency, behavioral family (a dotted segment where no population settles: the time average)
          (b) the critical transparency t* against caution, behavioral and syntactic families
The STYLE follows the figures already in the paper (R. Formenti's `OSGT Figure` and `Figure A`): default sans
font, viridis by caution level, left/bottom spines, legends above the axes.
"""
from __future__ import annotations

import glob
import json
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

APP = Path(__file__).resolve().parents[2] / "app"
ROOT = APP / "generated" / "egt_fine"
OUT = ROOT / "figures"
ALPHAS = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0]

# Style of the paper's existing figures: viridis by caution level, default sans font.
VIRIDIS = dict(zip(ALPHAS, ["#440154", "#414487", "#2a788e", "#22a884", "#7ad151", "#fde725"]))
MAXC, REPL, MINC = "#440154", "#5ec9ae", "#21918c"      # max Nash, replicator dynamics, min Nash
GRAY, LIGHTGRAY, TEXTGRAY = "#888888", "#b8b8b8", "#555555"

plt.rcParams.update({
    "font.family": "sans-serif", "font.size": 10.5, "mathtext.fontset": "dejavusans",
    "axes.spines.top": False, "axes.spines.right": False, "axes.linewidth": 1.0,
    "legend.frameon": False, "pdf.fonttype": 42,
})


def load(combo: str) -> dict[tuple[float, float], dict]:
    """(t, alpha) -> max / min equilibrium cooperation and the cooperation the sampled populations end with."""
    cyc_path = ROOT / combo / "cycling_time_averages.json"
    cycles = json.loads(cyc_path.read_text()) if cyc_path.exists() else {}
    pts: dict[tuple[float, float], dict] = {}
    for f in glob.glob(str(ROOT / combo / "runs" / "*" / "summary.json")):
        d = Path(f).parent
        s = json.loads(Path(f).read_text())
        comp = defaultdict(set)
        for line in (d / "nash" / "latest" / "equilibria.jsonl").read_text().splitlines():
            r = json.loads(line)
            comp[r["component_id"]].add(F(r["cooperation_rate_rational"]))
        levels = sorted({c for v in comp.values() for c in v})
        b = json.loads((d / "replicator" / "basins.json").read_text())
        n = b["n_interior_samples"]
        selected = 0.0
        for c in b["components"]:
            (level,) = comp[c["component_id"]]      # cooperation is constant on every component reached
            selected += c["n_interior"] / n * float(level)
        if b["n_unconverged"]:
            if d.name not in cycles:
                if b["n_unconverged"] / n > 0.02:
                    raise SystemExit(f"{d.name}: {b['n_unconverged']} of {n} starts unconverged and no time average")
            else:
                selected += b["n_unconverged"] / n * cycles[d.name]["time_avg_coop_mean"]
        rec = {"max": float(levels[-1]), "min": float(levels[0]), "full": levels[-1] == 1,
               "selected": selected, "cycling": bool(b["n_unconverged"] / n > 0.5), "levels": [str(x) for x in levels]}
        for t, a in s["grid_points"]:
            pts[(round(t, 2), round(a, 2))] = rec
    return pts


def thresholds(pts) -> dict[float, float]:
    out = {}
    for a in ALPHAS:
        ts = sorted(t for (t, aa) in pts if aa == a)
        full = [t for t in ts if pts[(t, a)]["full"]]
        tstar = min(full)
        assert all(pts[(t, a)]["full"] for t in ts if t >= tstar), f"alpha {a}: full cooperation is not a single switch"
        out[a] = tstar
    return out


beh, syn = load("behavioral_engine_side"), load("syntactic_engine_side")
TS = sorted({t for (t, a) in beh if a in ALPHAS})
assert len(TS) == 101 and all((t, a) in beh and (t, a) in syn for t in TS for a in ALPHAS)
tb, tsyn = thresholds(beh), thresholds(syn)
cycling = {a: [t for t in TS if beh[(t, a)]["cycling"]] for a in ALPHAS}
OUT.mkdir(parents=True, exist_ok=True)


# ---------------------------------------------------------------------------------------------- figure A
mean = lambda key: [sum(beh[(t, a)][key] for a in ALPHAS) / len(ALPHAS) for t in TS]  # noqa: E731
fig, ax = plt.subplots(figsize=(5.3, 4.15))
# A narrower, more saturated band than the original's: in the cycling windows the selected value sits about 5 pt
# below the maximum, and a 9 pt band covered that gap.
ax.step(TS, mean("selected"), where="post", color=REPL, linewidth=5, solid_joinstyle="round", solid_capstyle="butt",
        label="replicator dynamics", zorder=1)
ax.step(TS, mean("min"), where="post", color=MINC, linewidth=2.2, linestyle=(0, (1, 1.6)), label="min Nash", zorder=2)
ax.step(TS, mean("max"), where="post", color=MAXC, linewidth=1.9, solid_joinstyle="miter", label="max Nash", zorder=3)
# the six thresholds: one dot per caution level, in its colour of figure D, where the mean steps up by 1/6
for k, a in enumerate(ALPHAS, start=1):
    ax.plot([tb[a]], [k / 6], marker="o", markersize=7, color=VIRIDIS[a], markeredgecolor="white", markeredgewidth=0.9,
            zorder=5, clip_on=False)
    ax.annotate(rf"$\alpha={a:g}$", xy=(tb[a], k / 6), xytext=(-7, 1), textcoords="offset points", ha="right", va="center",
                fontsize=9.3, color=TEXTGRAY)
ax.set_xlim(-0.02, 1.02)
ax.set_ylim(-0.03, 1.03)
ax.set_xticks([0, 0.2, 0.4, 0.6, 0.8, 1.0])
ax.set_yticks([0, 0.2, 0.4, 0.6, 0.8, 1.0])
ax.set_xlabel("transparency $t$", fontsize=12)
ax.set_ylabel("cooperation at equilibrium", fontsize=12)
ax.text(0.98, 0.07, "replicator dynamics reach the maximum-\ncooperation program equilibrium from all\n"
        "starts, except on three narrow windows at\nlow transparency, where populations cycle",
        transform=ax.transAxes, ha="right", va="bottom", fontsize=9.3, color=TEXTGRAY, linespacing=1.35)
handles, labels = ax.get_legend_handles_labels()
order = [labels.index(x) for x in ("max Nash", "replicator dynamics", "min Nash")]
ax.legend([handles[i] for i in order], [labels[i] for i in order], loc="lower center", bbox_to_anchor=(0.5, 1.0),
          ncol=3, fontsize=11, handlelength=1.8, columnspacing=1.4, borderaxespad=0.3)
fig.tight_layout(pad=0.5)
fig.savefig(OUT / "figure_A.pdf")
fig.savefig(OUT / "figure_A.png", dpi=250)
plt.close(fig)

# ---------------------------------------------------------------------------------------------- figure D
fig = plt.figure(figsize=(10.6, 4.9))
outer = fig.add_gridspec(1, 2, width_ratios=[1.72, 1.0], wspace=0.17, left=0.065, right=0.985, bottom=0.115, top=0.875)
inner = outer[0].subgridspec(2, 3, wspace=0.10, hspace=0.26)
axes = []
for k, a in enumerate(ALPHAS):
    ax = fig.add_subplot(inner[k // 3, k % 3])
    axes.append(ax)
    c, x = VIRIDIS[a], tb[a]
    assert all(abs(beh[(t, a)]["selected"] - 1.0) < 1e-9 for t in TS if t >= x), f"alpha {a}: not all populations cooperate above t*"
    win = cycling[a]
    assert all(beh[(t, a)]["selected"] < 1e-9 for t in TS if t < x and t not in win), f"alpha {a}: cooperation below t*"
    # defection below t* (broken at the window where no population settles), full cooperation from t* on
    lo, hi = (win[0], win[-1] + 0.01) if win else (None, None)
    for x0, x1 in ([(0.0, lo), (hi, x)] if win else [(0.0, x)]):
        ax.plot([x0, x1], [0, 0], color=c, linewidth=2.4, solid_capstyle="butt")
    if x < 1.0:
        ax.plot([x, 1.0], [1, 1], color=c, linewidth=2.4, solid_capstyle="butt")
    ax.plot([x, x], [0, 1], color=c, linewidth=1.5, linestyle=(0, (3, 2)))
    ax.plot([x], [1], marker="o", markersize=6.5, color=c, clip_on=False, zorder=4)
    if win:
        level = sum(beh[(t, a)]["selected"] for t in win) / len(win)     # the long-run time average, about 0.2
        ax.plot([lo, hi], [level, level], color=c, linewidth=2.4, solid_capstyle="butt")
        ax.plot([lo, lo], [0, level], color=c, linewidth=1.0, linestyle=(0, (1, 1)))
        ax.plot([hi, hi], [0, level], color=c, linewidth=1.0, linestyle=(0, (1, 1)))
        ax.text((lo + hi) / 2, level + 0.06, "cycles", ha="center", va="bottom", fontsize=8.5, color=TEXTGRAY)
    left = x > 0.6
    ax.text(x + (-0.05 if left else 0.05), 0.5, rf"$t^*={x:g}$", ha="right" if left else "left", va="center",
            fontsize=10, color=TEXTGRAY)
    ax.set_title(rf"$\alpha={a:g}$", fontsize=12, pad=6)
    ax.set_xlim(-0.04, 1.04)
    ax.set_ylim(-0.07, 1.09)
    ax.set_xticks([0, 0.5, 1])
    ax.set_yticks([0, 0.5, 1])
    ax.set_xticklabels(["0", "0.5", "1"] if k >= 3 else [])
    ax.set_yticklabels(["0", "0.5", "1"] if k % 3 == 0 else [])
box = outer[0].get_position(fig)
fig.text(box.x0 - 0.048, (box.y0 + box.y1) / 2, "cooperation at equilibrium", rotation=90, ha="center", va="center", fontsize=12)
fig.text((box.x0 + box.x1) / 2, 0.022, "transparency $t$", ha="center", va="bottom", fontsize=12)
fig.legend([plt.Line2D([0], [0], color="#444444", linewidth=2.6)], ["replicator dynamics"], loc="upper center",
           bbox_to_anchor=((box.x0 + box.x1) / 2, 1.0), fontsize=10.5, handlelength=2.2, borderaxespad=0.25)
fig.text(0.004, 0.995, "(a)", fontsize=13, fontweight="bold", ha="left", va="top")

a2 = fig.add_subplot(outer[1])
a2.plot(ALPHAS, [tsyn[a] for a in ALPHAS], color=LIGHTGRAY, linewidth=1.5, linestyle=(0, (4, 2.5)), label="syntactic", zorder=1)
# the six syntactic thresholds as grey dots, for comparison with the coloured behavioral ones
a2.plot(ALPHAS, [tsyn[a] for a in ALPHAS], linestyle="none", marker="o", markersize=6, color="#9a9a9a",
        markeredgecolor="white", markeredgewidth=0.8, zorder=2, clip_on=False)
a2.plot(ALPHAS, [tb[a] for a in ALPHAS], color=GRAY, linewidth=1.5, label="behavioral", zorder=3)
for a in ALPHAS:
    a2.plot([a], [tb[a]], marker="o", markersize=7, color=VIRIDIS[a], zorder=4, clip_on=False)
a2.text(0.5, 0.91, "cooperation", fontsize=10.5, color=TEXTGRAY, ha="left", va="center")
a2.text(1.0, 0.09, "defection", fontsize=10.5, color=TEXTGRAY, ha="right", va="center")
a2.set_xlim(0.47, 1.03)
a2.set_ylim(-0.03, 1.03)
a2.set_xticks(ALPHAS)
a2.set_yticks([0, 0.2, 0.4, 0.6, 0.8, 1.0])
a2.set_xlabel(r"caution $\alpha$", fontsize=12)
a2.set_ylabel(r"critical transparency $t^*$", fontsize=12)
h, l = a2.get_legend_handles_labels()
a2.legend([h[1], h[0]], [l[1], l[0]], loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=2, fontsize=10.5,
          handlelength=2.4, columnspacing=1.6, borderaxespad=0.3)
bbox = a2.get_position()
fig.text(bbox.x0 - 0.062, 0.995, "(b)", fontsize=13, fontweight="bold", ha="left", va="top")
fig.savefig(OUT / "figure_D.pdf")
fig.savefig(OUT / "figure_D.png", dpi=200)
plt.close(fig)

(OUT / "figure_data.json").write_text(json.dumps({
    "t": TS, "alphas": ALPHAS,
    "behavioral": {"t_star": tb, "cycling_t": cycling,
                   "mean_max": mean("max"), "mean_min": mean("min"), "mean_selected": mean("selected"),
                   "selected": {str(a): [beh[(t, a)]["selected"] for t in TS] for a in ALPHAS}},
    "syntactic": {"t_star": tsyn},
}, indent=1))
print("behavioral t*:", tb)
print("syntactic  t*:", tsyn)
print("cycling windows (behavioral):", {a: (v[0], v[-1]) for a, v in cycling.items() if v})
print("wrote", OUT)

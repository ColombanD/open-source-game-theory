"""Every number of the paper's experiments section, read from `app/paper_results/`.

Run from `app/`:

    uv run python -m pd_runner.paper.numbers

Prints the numbers under the title of the paper section that quotes them. Nothing is recomputed here except
counting: the equilibria, the component of each one and the end point of each sampled population are in the
snapshot (`pd_runner.paper.snapshot` builds it from the sweep output). `tests/test_paper_numbers.py` pins the
values the paper states.
"""
from __future__ import annotations

import json
from fractions import Fraction

from pd_runner.egt.replicator.basins import wilson_interval
from pd_runner.paper import LIBRARIES, RESULTS, SIDES

CAUTIONS = [0.5, 0.6, 0.7, 0.8, 0.9, 1.0]       # the six caution levels the paper reports
LOW_CAUTIONS = [0.0, 0.2, 0.4]                  # swept as well, negative side only


# ------------------------------------------------------------------------------------------ full transparency

def load_game(library: str, side: str = "engine_side") -> dict:
    return json.loads((RESULTS / "full_transparency" / f"{library}__{side}.json").read_text())


def components(game: dict) -> list[dict]:
    """The equilibrium components of a game, most cooperative first.

    `strategies`: the distinct mixes a player uses at an extreme equilibrium of the component. Any two of them,
    one per player, form an extreme equilibrium, which is how the paper's table lists them.
    """
    out: dict[int, dict] = {}
    for e in game["equilibria"]:
        c = out.setdefault(e["component"], {"id": e["component"], "n_extreme": 0, "cooperation": set(),
                                            "payoffs": set(), "strategies": []})
        c["n_extreme"] += 1
        c["cooperation"].add(Fraction(e["cooperation"]))
        c["payoffs"] |= {Fraction(e["row_payoff"]), Fraction(e["col_payoff"])}
        for mix in (e["row"], e["col"]):
            if mix not in c["strategies"]:
                c["strategies"].append(mix)
    for c in out.values():
        c["programs"] = sorted({p for s in c["strategies"] for p in s})
        c["strategies"].sort(key=lambda s: (len(s), sorted(s)))
    return sorted(out.values(), key=lambda c: -max(c["cooperation"]))


def cooperative_component(game: dict) -> dict:
    (full,) = [c for c in components(game) if c["cooperation"] == {Fraction(1)}]
    return full


def selection(game: dict) -> dict:
    """Where the 1,000 uniformly drawn populations end, by equilibrium component."""
    u = game["uniform_starts"]
    level = {c["id"]: max(c["cooperation"]) for c in components(game)}
    rows = [{"cooperation": level[r["component"]], "n": r["n"],
             "ci95": wilson_interval(r["n"], u["n"]),
             "n_still_invadable": r["n_at_last_horizon_with_an_invader"]} for r in u["by_component"]]
    full = sum(r["n"] for r in rows if r["cooperation"] == 1)
    return {"n": u["n"], "n_full_cooperation": full, "ci95_full_cooperation": wilson_interval(full, u["n"]),
            "n_unconverged": u["n_unconverged"], "by_component": rows, "by_support": u["by_support"],
            "share_range": u["final_share_range"]}


# --------------------------------------------------------------------------------------- partial transparency

def load_sweep(family: str, side: str = "engine_side") -> dict[tuple[float, float], dict]:
    """(t, alpha) -> the game played at that grid point."""
    games = json.loads((RESULTS / "partial_transparency" / f"{family}_{side}.json").read_text())
    points = {}
    for g in games:
        level = {c["id"]: [Fraction(x) for x in c["cooperation"]] for c in g["components"]}
        rep = g["replicator"]
        rec = {
            "levels": sorted({x for v in level.values() for x in v}),
            "n": rep["n"],
            # populations that settled, by the cooperation of the component they reached
            "reached": {max(level[r["id"]]): r["n"] for r in rep["reached"]},
            "n_unsettled": rep["n_unconverged"],
            "cycle": g.get("cycle"),
        }
        assert all(len(level[r["id"]]) == 1 for r in rep["reached"]), g["run"]
        for t, a in g["grid_points"]:
            points[(t, a)] = rec
    return points


def transparencies(points: dict, alpha: float) -> list[float]:
    return sorted(t for (t, a) in points if a == alpha)


def first_appearance(points: dict, alpha: float, level: Fraction) -> float | None:
    """The lowest sampled transparency at which an equilibrium with that cooperation exists."""
    hits = [t for t in transparencies(points, alpha) if level in points[(t, alpha)]["levels"]]
    return min(hits) if hits else None


def is_single_switch(points: dict, alpha: float) -> bool:
    """Full cooperation is an equilibrium at every sampled transparency from its first appearance on."""
    t_star = first_appearance(points, alpha, Fraction(1))
    return t_star is not None and all(
        Fraction(1) in points[(t, alpha)]["levels"] for t in transparencies(points, alpha) if t >= t_star)


def share(points: dict, t: float, alpha: float, level) -> float:
    """Share of the sampled populations that settle on an equilibrium with that cooperation."""
    p = points[(t, alpha)]
    return p["reached"].get(Fraction(level), 0) / p["n"]


def intervals(ts: list[float]) -> list[tuple[float, float]]:
    """Maximal runs of consecutive grid points (spacing 0.01)."""
    out: list[list[float]] = []
    for t in sorted(ts):
        if out and round(t - out[-1][1], 2) == 0.01:
            out[-1][1] = t
        else:
            out.append([t, t])
    return [(a, b) for a, b in out]


def unsettled_windows(points: dict, alpha: float) -> list[tuple[float, float]]:
    """Transparency ranges where more than half of the sampled populations do not settle."""
    return intervals([t for t in transparencies(points, alpha)
                      if 2 * points[(t, alpha)]["n_unsettled"] > points[(t, alpha)]["n"]])


def cell_label(levels: list[Fraction]) -> str:
    """The label of the paper's table of equilibrium outcomes."""
    known = {(0,): "DEF", (0, 1): "BOTH", (0, Fraction(11, 18), 1): "ALL"}
    return known.get(tuple(levels), "Pr[(C,C)] in {" + ", ".join(str(x) for x in levels) + "}")


# ------------------------------------------------------------------------------------------------- the report

def _mix(s: dict) -> str:
    return ", ".join(f"{p} {w}" for p, w in sorted(s.items()))


def _iv(ci) -> str:
    return f"[{ci[0]:.4f}, {ci[1]:.4f}]"


def _ranges(iv: list[tuple[float, float]]) -> str:
    return ", ".join(f"{a:.2f}" if a == b else f"[{a:.2f}, {b:.2f}]" for a, b in iv) or "none"


def report() -> str:
    L: list[str] = []
    say = L.append

    def head(title: str) -> None:
        say("")
        say(title)
        say("-" * len(title))

    sigma = load_game("body8")
    say("Read from " + str(RESULTS) + ". In file names, "
        + " and ".join(f"{code} is the {name}" for code, name in SIDES.items()) + ".")
    say("")
    say("FULL TRANSPARENCY")

    head("Enumerating Program Equilibria; appendix, An Enumeration of Program Equilibria")
    comps = components(sigma)
    say(f"Library Sigma, negative side: {len(sigma['equilibria'])} extreme equilibria in {len(comps)} components.")
    for c in comps:
        (coop,) = c["cooperation"]
        say(f"  Pr[(C,C)] = {coop}: {c['n_extreme']} extreme equilibria, payoffs {sorted(map(str, c['payoffs']))}")
        for s in c["strategies"]:
            say(f"      {_mix(s)}")
    full = cooperative_component(sigma)
    weight = min(Fraction(s.get("DupocBot", 0)) for s in full["strategies"])
    say(f"  Lowest weight of DupocBot in a strategy of the fully cooperative component: {weight}")

    head("Appendix, Replicator Dynamics at Full Transparency")
    sel = selection(sigma)
    say(f"Library Sigma, negative side, {sel['n']} uniformly drawn populations, "
        f"{sel['n'] - sel['n_unconverged']} converged.")
    for r in sel["by_component"]:
        say(f"  Pr[(C,C)] = {r['cooperation']}: {r['n']} populations, 95% Wilson interval {_iv(r['ci95'])}")
    say(f"  A component no population reaches: 95% Wilson interval {_iv(wilson_interval(0, sel['n']))}")
    say("  Programs present at the end (share at least 1e-6):")
    for s in sel["by_support"]:
        say(f"      {', '.join(s['present']):45s} {s['n']}")
    lo, hi = sel["share_range"]["DupocBot"]
    say(f"  Final share of DupocBot: from {lo:.4f} to {hi:.4f}")

    head("Appendix, Sensitivity to the Program Library")
    say(f"  {'library':40s} {'components':>10s} {'extreme':>8s} {'coop. share':>12s}  cooperative support")
    for key, name in LIBRARIES.items():
        g = load_game(key)
        cs, s = components(g), selection(g)
        say(f"  {name:40s} {len(cs):>10d} {len(g['equilibria']):>8d} {100 * s['n_full_cooperation'] / s['n']:>11.1f}%"
            f"  {', '.join(cooperative_component(g)['programs'])}")
        say(f"  {'':40s} Pr[(C,C)] by component: {', '.join(str(max(c['cooperation'])) for c in cs)}")
        for r in s["by_component"]:
            if r["cooperation"] != 1:
                say(f"  {'':40s} {r['n']} populations at Pr[(C,C)] = {r['cooperation']} at the last horizon "
                    f"({r['n_still_invadable']} of them at a state a rare program still invades); "
                    f"{s['n_unconverged']} unconverged")

    head("Appendix, Sensitivity to the Hinge")
    pos = load_game("body8", "hinge_side")
    cs, s = components(pos), selection(pos)
    say(f"Library Sigma, positive side: {len(pos['equilibria'])} extreme equilibria in {len(cs)} components, "
        f"Pr[(C,C)] = {', '.join(str(max(c['cooperation'])) for c in cs)}.")
    say(f"  Fully cooperative component: programs {', '.join(cooperative_component(pos)['programs'])}")
    for r in s["by_component"]:
        say(f"  Pr[(C,C)] = {r['cooperation']}: {r['n']} of {s['n']} populations, 95% Wilson interval {_iv(r['ci95'])}"
            + (f" ({r['n_still_invadable']} at a state a rare program still invades)"
               if r["n_still_invadable"] else ""))

    say("")
    say("")
    say("PARTIAL TRANSPARENCY (library Sigma, transparency grid 0, 0.01, ..., 1)")
    beh, syn = load_sweep("behavioral"), load_sweep("syntactic")

    head("Equilibrium Cooperation and Selection; appendix, Equilibrium under Partial Transparency")
    say("Behavioral family, negative side. t* = first fully cooperative equilibrium, t** = first equilibrium with")
    say("Pr[(C,C)] = 11/18. 'above' = lowest share of populations reaching full cooperation at any t >= t*.")
    say(f"  {'caution':>7s} {'t*':>5s} {'t**':>5s} {'single switch':>14s} {'above':>6s}   every tenth grid point")
    for a in CAUTIONS:
        t1, t2 = first_appearance(beh, a, Fraction(1)), first_appearance(beh, a, Fraction(11, 18))
        ts = transparencies(beh, a)
        above = min(share(beh, t, a, 1) for t in ts if t >= t1)
        row = " ".join(f"{cell_label(beh[(t, a)]['levels']):>4s}" for t in ts if round(t * 100) % 10 == 0)
        say(f"  {a:>7.1f} {t1:>5.2f} {t2:>5.2f} {str(is_single_switch(beh, a)):>14s} {above:>6.3f}   {row}")
    say("  Below t*, populations that do not all settle on mutual defection:")
    for a in CAUTIONS:
        for lo, hi in unsettled_windows(beh, a):
            window = [beh[(t, a)] for t in transparencies(beh, a) if lo <= t <= hi]
            p = window[0]
            assert all(q["levels"] == p["levels"] and q["n_unsettled"] == q["n"] for q in window)
            averages = sorted(q["cycle"]["time_average_cooperation"] for q in window)
            say(f"      caution {a}: t in {_ranges([(lo, hi)])}: equilibria at Pr[(C,C)] = "
                f"{', '.join(map(str, p['levels']))}; no sampled population settles; they cycle among "
                f"{', '.join(p['cycle']['programs'])}, long-run Pr[(C,C)] {averages[0]:.3f} to {averages[-1]:.3f}")
    say(f"  Caution 0.8: equilibria at t = 0.47: {cell_label(beh[(0.47, 0.8)]['levels'])}; at t = 0.48: "
        f"{cell_label(beh[(0.48, 0.8)]['levels'])}, {100 * share(beh, 0.48, 0.8, 1):.0f}% of populations reach "
        f"full cooperation")
    say("  Lower caution levels (swept, not reported in the figures): t* = "
        + ", ".join(f"{first_appearance(beh, a, Fraction(1)):.2f} at caution {a}" for a in LOW_CAUTIONS))

    head("Appendix, Sensitivity to the Transparency Map and the Hinge")
    say("Syntactic family, negative side.")
    say(f"  {'caution':>7s} {'t*':>5s} {'single switch':>14s} {'above':>6s} {'defection below':>16s}")
    for a in CAUTIONS:
        t1 = first_appearance(syn, a, Fraction(1))
        ts = transparencies(syn, a)
        above = min(share(syn, t, a, 1) for t in ts if t >= t1)
        below = min((share(syn, t, a, 0) for t in ts if t < t1), default=float("nan"))
        say(f"  {a:>7.1f} {t1:>5.2f} {str(is_single_switch(syn, a)):>14s} {above:>6.3f} {below:>16.3f}")
    say(f"  Populations that do not settle anywhere: "
        f"{_ranges([w for a in CAUTIONS for w in unsettled_windows(syn, a)])}")
    for family in ("behavioral", "syntactic"):
        pts = load_sweep(family, "hinge_side")
        say(f"Positive side, {family} family: where a fully cooperative equilibrium exists, and what holds elsewhere")
        for a in CAUTIONS:
            ts = transparencies(pts, a)
            full = intervals([t for t in ts if Fraction(1) in pts[(t, a)]["levels"]])
            rest: dict[str, list[float]] = {}
            for t in ts:
                if Fraction(1) not in pts[(t, a)]["levels"]:
                    rest.setdefault(cell_label(pts[(t, a)]["levels"]), []).append(t)
            elsewhere = "; ".join(f"{label} on {_ranges(intervals(v))}" for label, v in rest.items())
            say(f"  caution {a}: full cooperation on {_ranges(full)}; {elsewhere}; at t = 1, "
                f"{100 * share(pts, 1.0, a, 1):.1f}% of populations reach full cooperation")
    return "\n".join(L)


def main() -> None:
    print(report())


if __name__ == "__main__":
    main()

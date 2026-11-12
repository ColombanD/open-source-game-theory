"""The numbers the paper's experiments section states, pinned against the tracked snapshot `app/paper_results/`.

A failure here means the snapshot and the paper disagree: either a sweep was re-run and re-snapshotted with a
different result (then the paper's text must follow), or the snapshot was edited by hand.
"""
from fractions import Fraction as F

import pytest

from pd_runner.paper import LIBRARIES
from pd_runner.paper.numbers import (
    CAUTIONS,
    cell_label,
    components,
    cooperative_component,
    first_appearance,
    is_single_switch,
    load_game,
    load_sweep,
    report,
    selection,
    share,
    transparencies,
    unsettled_windows,
)

COOP = ["CooperateBot", "DupocBot", "TitForTatBot"]


def test_sigma_equilibria():
    game = load_game("body8")
    comps = components(game)
    assert len(game["equilibria"]) == 21
    assert [(max(c["cooperation"]), c["n_extreme"]) for c in comps] == [(1, 16), (F(11, 18), 1), (0, 4)]
    assert all(len(c["cooperation"]) == 1 for c in comps)
    full, partial, defect = comps
    assert full["programs"] == COOP and len(full["strategies"]) == 4
    assert min(F(s.get("DupocBot", 0)) for s in full["strategies"]) == F(1, 9)
    assert partial["strategies"] == [{"CooperateBot": "1/2", "EBot": "1/6", "OBot": "1/3"}]
    assert partial["payoffs"] == {F(3, 2)}
    assert defect["programs"] == ["DefectBot", "OBot"]


def test_sigma_selection():
    sel = selection(load_game("body8"))
    assert (sel["n"], sel["n_full_cooperation"], sel["n_unconverged"]) == (1000, 1000, 0)
    assert [round(x, 4) for x in sel["ci95_full_cooperation"]] == [0.9962, 1.0]
    assert [(s["present"], s["n"]) for s in sel["by_support"]] == [
        (COOP, 955), (["DupocBot", "TitForTatBot"], 30), (["DupocBot"], 8), (["CooperateBot", "DupocBot"], 7)]
    assert round(sel["share_range"]["DupocBot"][0], 4) == 0.1524


@pytest.mark.parametrize("library, n_extreme, n_full, support", [
    ("nonprovers+dupoc", 21, 1000, COOP),
    ("body8", 21, 1000, COOP),
    ("body8+trolls", 35, 975, COOP),
    ("body8+trolls+provers", 69, 1000, ["CIMCIC"] + COOP),
])
def test_library_ladder(library, n_extreme, n_full, support):
    game = load_game(library)
    assert library in LIBRARIES
    assert len(game["equilibria"]) == n_extreme
    assert [max(c["cooperation"]) for c in components(game)] == [1, F(11, 18), 0]
    assert cooperative_component(game)["programs"] == support
    assert selection(game)["n_full_cooperation"] == n_full


def test_ten_program_library_slow_escapes():
    sel = selection(load_game("body8+trolls"))
    (defect,) = [r for r in sel["by_component"] if r["cooperation"] == 0]
    assert (defect["n"], defect["n_still_invadable"], sel["n_unconverged"]) == (23, 23, 2)


def test_positive_side_of_the_hinge():
    game = load_game("body8", "hinge_side")
    assert len(game["equilibria"]) == 16
    assert [max(c["cooperation"]) for c in components(game)] == [1, F(11, 18), F(14, 27), F(43, 147), 0]
    assert cooperative_component(game)["programs"] == COOP
    sel = selection(game)
    assert sel["n_full_cooperation"] == 959
    assert [round(x, 3) for x in sel["ci95_full_cooperation"]] == [0.945, 0.970]
    (defect,) = [r for r in sel["by_component"] if r["cooperation"] != 1]
    assert (defect["cooperation"], defect["n"], defect["n_still_invadable"]) == (0, 41, 41)


def test_behavioral_thresholds():
    pts = load_sweep("behavioral")
    assert len(transparencies(pts, 0.5)) == 101
    assert [first_appearance(pts, a, F(1)) for a in CAUTIONS] == [0.14, 0.29, 0.44, 0.48, 0.66, 1.0]
    assert [first_appearance(pts, a, F(11, 18)) for a in CAUTIONS] == [0.26, 0.35, 0.46, 0.71, 0.88, 1.0]
    for a in CAUTIONS:
        t_star = first_appearance(pts, a, F(1))
        assert is_single_switch(pts, a)
        # at and above the threshold every sampled population reaches full cooperation; below it none does
        assert all(share(pts, t, a, 1) == 1 for t in transparencies(pts, a) if t >= t_star)
        assert all(share(pts, t, a, 1) == 0 for t in transparencies(pts, a) if t < t_star)
    assert cell_label(pts[(0.47, 0.8)]["levels"]) == "DEF" and cell_label(pts[(0.48, 0.8)]["levels"]) == "BOTH"


def test_behavioral_table_rows():
    pts = load_sweep("behavioral")
    rows = {a: [cell_label(pts[(t / 10, a)]["levels"]) for t in range(11)] for a in CAUTIONS}
    assert rows[0.5] == ["DEF", "DEF", "BOTH"] + ["ALL"] * 8
    assert rows[0.6] == ["DEF"] * 3 + ["BOTH"] + ["ALL"] * 7
    assert rows[0.7] == ["DEF"] * 5 + ["ALL"] * 6
    assert rows[0.8] == ["DEF"] * 5 + ["BOTH"] * 3 + ["ALL"] * 3
    assert rows[0.9] == ["DEF"] * 7 + ["BOTH"] * 2 + ["ALL"] * 2
    assert rows[1.0] == ["DEF"] * 10 + ["ALL"]


def test_cycling_windows():
    pts = load_sweep("behavioral")
    assert {a: unsettled_windows(pts, a) for a in CAUTIONS} == {
        0.5: [], 0.6: [], 0.7: [(0.03, 0.03)], 0.8: [(0.13, 0.15)], 0.9: [(0.34, 0.37)], 1.0: []}
    for t, a in [(0.03, 0.7), (0.13, 0.8), (0.14, 0.8), (0.15, 0.8), (0.34, 0.9), (0.37, 0.9)]:
        p = pts[(t, a)]
        assert p["levels"] == [0, F(1, 6), F(1, 3)]
        assert p["cycle"]["programs"] == ["CupodBot", "DupocBot", "EBot", "TitForTatBot"]
        assert abs(p["cycle"]["time_average_cooperation"] - 0.2) < 0.01
    # elsewhere below the threshold, every sampled population settles on mutual defection
    for a in CAUTIONS:
        windows = unsettled_windows(pts, a)
        for t in transparencies(pts, a):
            if t < first_appearance(pts, a, F(1)) and not any(lo <= t <= hi for lo, hi in windows):
                assert share(pts, t, a, 0) == 1, (t, a)


def test_syntactic_thresholds():
    pts = load_sweep("syntactic")
    assert [first_appearance(pts, a, F(1)) for a in CAUTIONS] == [0.07, 0.20, 0.37, 0.57, 0.79, 1.0]
    for a in CAUTIONS:
        t_star = first_appearance(pts, a, F(1))
        assert is_single_switch(pts, a) and unsettled_windows(pts, a) == []
        assert all(share(pts, t, a, 1) == 1 for t in transparencies(pts, a) if t >= t_star)
        assert all(share(pts, t, a, 0) == 1 for t in transparencies(pts, a) if t < t_star)


@pytest.mark.parametrize("family", ["behavioral", "syntactic"])
def test_positive_side_has_no_single_threshold(family):
    pts = load_sweep(family, "hinge_side")
    assert not all(is_single_switch(pts, a) for a in CAUTIONS)
    # full cooperation is still an equilibrium, and selected by most populations, at full transparency
    assert all(F(1) in pts[(1.0, a)]["levels"] and share(pts, 1.0, a, 1) > 0.95 for a in CAUTIONS)


def test_report_runs():
    text = report()
    assert "21 extreme equilibria in 3 components" in text and "PARTIAL TRANSPARENCY" in text


# ------------------------------------------------------------------ the chain from the Lean export to the games

PAYOFF = {"CC": 2, "CD": -1, "DC": 3, "DD": 0}       # the row player's payoff: T = 3, R = 2, P = 0, S = -1


@pytest.mark.parametrize("library, side", [
    ("nonprovers+dupoc", "engine_side"), ("body8", "engine_side"), ("body8+trolls", "engine_side"),
    ("body8+trolls+provers", "engine_side"), ("body8", "hinge_side")])
def test_games_are_the_lean_export(library, side):
    """The payoff matrix of every snapshot game is the one the exported theorems give, hinge cells included."""
    import warnings

    from pd_runner.tau.matrix import load_tau_matrix

    game = load_game(library, side)
    programs = game["programs"]
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        m = load_tau_matrix(tuple(programs), source="sprime", floor_policy=side)
    cells = {(r, c): m.cell(r, c) for r in programs for c in programs}
    assert game["payoff_matrix"] == [[PAYOFF[cells[(r, c)].row_action + cells[(r, c)].col_action] for c in programs]
                                     for r in programs]
    assert sorted(game["hinge_cells"]) == sorted([r, c] for (r, c), cell in cells.items() if cell.is_floor)


def test_outcome_matrix_pairs():
    from pd_runner.paper.matrix import pairs

    sigma = pairs("body8")
    assert len(sigma) == 36
    assert {(p["row"], p["col"]) for p in sigma if p["hinge"]} == {("DBot", "DupocBot"), ("EBot", "DupocBot")}
    assert all(p["positive_side"] == "CC" for p in sigma if p["hinge"])
    red = next(p for p in sigma if (p["row"], p["col"]) == ("DupocBot", "CupodBot"))
    assert (red["outcome"], red["regime"], red["theorem"]) == ("DC", "every budget k", "outcome_DupocBot_vs_CupodBot")
    assert red["file"] == "arith/ArithS/Outcome/Matrix/DupocBot.lean"
    twelve = pairs("body8+trolls+provers")
    assert (len(twelve), sum(p["hinge"] for p in twelve)) == (78, 9)

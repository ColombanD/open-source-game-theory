"""Tests for pure-strategy ESS enumeration on a row-player payoff matrix."""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

import numpy as np
import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

from pd_runner.egt.ingest import (  # noqa: E402
    payoff_matrix_from_cells,
    payoff_matrix_from_tau_matrix,
)
from pd_runner.egt.static_analysis.cli import (  # noqa: E402
    build_assumptions,
    suspect_cells_for,
)
from pd_runner.egt.static_analysis.ess import (  # noqa: E402
    enumerate_pure_ess,
    flag_suspect_cells,
)
from pd_runner.egt.static_analysis.reporting import write_all  # noqa: E402


def _summary(result, name):
    for s in result.summary:
        if s.type == name:
            return s
    raise KeyError(name)


def _pair(result, i, j):
    for r in result.pairwise:
        if r.i == i and r.j == j:
            return r
    raise KeyError((i, j))


# --- 1. All-defect dominance ---------------------------------------------

def test_all_defect_dominance():
    """In the 2x2 PD with b=3, c=1, DefectBot is the unique pure ESS."""
    names = ["C", "D"]
    b, c = 3.0, 1.0
    A = np.array([[b - c, -c], [b, 0.0]])  # row C, row D

    r = enumerate_pure_ess(names, A)

    assert _summary(r, "D").is_ESS
    assert not _summary(r, "C").is_ESS

    p_dc = _pair(r, "D", "C")
    assert p_dc.clause_a_holds and p_dc.i_survives_j

    p_cd = _pair(r, "C", "D")
    assert not p_cd.i_survives_j
    assert not p_cd.tie_at_ji


# --- 2. Rock-paper-scissors: empty ESS ----------------------------------

def test_rps_empty_ess():
    names = ["R", "P", "S"]
    A = np.array(
        [
            [0.0, -1.0, 1.0],
            [1.0, 0.0, -1.0],
            [-1.0, 1.0, 0.0],
        ]
    )
    r = enumerate_pure_ess(names, A)
    assert all(not s.is_ESS for s in r.summary)
    assert len(r.pairwise) == 6


# --- 3. Tiebreaker resolved by clause (b) -------------------------------

def test_tiebreaker_clause_b_resolves():
    names = ["0", "1"]
    A = np.array([[1.0, 2.0], [1.0, 0.0]])

    r = enumerate_pure_ess(names, A)
    p01 = _pair(r, "0", "1")
    assert p01.tie_at_ji
    assert not p01.clause_a_holds
    assert p01.clause_b_holds
    assert p01.i_survives_j

    assert _summary(r, "0").is_ESS
    assert not _summary(r, "1").is_ESS


# --- 4. Tiebreaker fails clause (b) -------------------------------------

def test_tiebreaker_clause_b_fails():
    names = ["0", "1"]
    A = np.array([[1.0, 0.0], [1.0, 2.0]])

    r = enumerate_pure_ess(names, A)
    p01 = _pair(r, "0", "1")
    assert p01.tie_at_ji
    assert not p01.clause_a_holds
    assert not p01.clause_b_holds
    assert not p01.i_survives_j

    assert not _summary(r, "0").is_ESS


# --- 5. No symmetrisation -----------------------------------------------

def test_no_symmetrisation():
    """An asymmetric A whose ESS verdict changes under (A + A.T)/2."""
    names = ["0", "1"]
    A = np.array([[2.0, 5.0], [1.0, 0.0]])
    # Raw: A[0,0]=2 > A[1,0]=1 → type 0 survives 1 via (a) → 0 is ESS.
    # Symmetrised: A_sym[1,0] = (5+1)/2 = 3 > A_sym[0,0]=2 → 0 not ESS.
    r = enumerate_pure_ess(names, A)
    assert _summary(r, "0").is_ESS

    A_sym = (A + A.T) / 2.0
    r_sym = enumerate_pure_ess(names, A_sym)
    assert not _summary(r_sym, "0").is_ESS


# --- 6. Tolerance absorbs float noise -----------------------------------

def test_tolerance_absorbs_float_noise():
    names = ["0", "1"]
    A = np.array([[1.0 + 1e-15, 2.0], [1.0, 0.0]])
    r = enumerate_pure_ess(names, A, atol=1e-12)
    p01 = _pair(r, "0", "1")
    assert p01.tie_at_ji
    assert p01.clause_b_holds


# --- 7. N=1 degenerate --------------------------------------------------

def test_single_type_is_trivially_ess():
    r = enumerate_pure_ess(["only"], np.array([[42.0]]))
    assert len(r.pairwise) == 0
    assert _summary(r, "only").is_ESS


def test_empty_matrix_raises():
    with pytest.raises(ValueError):
        enumerate_pure_ess([], np.zeros((0, 0)))


def test_non_finite_value_raises():
    with pytest.raises(ValueError):
        enumerate_pure_ess(
            ["x", "y"], np.array([[float("nan"), 0.0], [0.0, 0.0]])
        )


# --- 8. Schema regression ------------------------------------------------

def test_writers_roundtrip(tmp_path):
    names = ["C", "D"]
    A = np.array([[2.0, -1.0], [3.0, 0.0]])
    r = enumerate_pure_ess(names, A)
    r = flag_suspect_cells(r, [])

    payoff = payoff_matrix_from_cells(
        names,
        {
            ("C", "C"): ("C", "C"),
            ("C", "D"): ("C", "D"),
            ("D", "C"): ("D", "C"),
            ("D", "D"): ("D", "D"),
        },
        b=3.0,
        c=1.0,
    )
    assumptions = build_assumptions(payoff, atol=1e-12)
    write_all(r, names, A, assumptions, tmp_path)

    with open(tmp_path / "ess_summary.csv") as f:
        rows = list(csv.DictReader(f))
    assert {row["type"] for row in rows} == {"C", "D"}
    assert next(row for row in rows if row["type"] == "D")["is_ESS"] == "True"
    assert next(row for row in rows if row["type"] == "C")["is_ESS"] == "False"

    with open(tmp_path / "ess_pairwise.csv") as f:
        pwrows = list(csv.DictReader(f))
    assert len(pwrows) == 2  # N*(N-1)

    expected_cols = [
        "i", "j",
        "A_ii", "A_ji", "A_ij", "A_jj",
        "clause_a_holds", "tie_at_ji", "clause_b_holds",
        "i_survives_j", "touches_suspect_cell",
    ]
    assert list(pwrows[0].keys()) == expected_cols

    with open(tmp_path / "assumptions.json") as f:
        a = json.load(f)
    assert a["pd_payoffs"]["implied_trps"] == {
        "T": 3.0, "R": 2.0, "P": 0.0, "S": -1.0,
    }
    assert (tmp_path / "payoff_matrix_numeric.csv").exists()
    assert (tmp_path / "report.md").exists()


# --- 9. Real-data smoke test --------------------------------------------

@pytest.mark.parametrize("zoo_key", ["default", "enlarged"])
def test_real_data_smoke(zoo_key):
    """The ESS stage over a real, Lean-certified zoo.

    Rebased from the standalone repo's hand-transcribed 8-bot CSV. The
    assertions that survive are the ones that follow from the PD convention
    rather than from that particular matrix.
    """
    from pd_runner.tau.matrix import get_zoo

    payoff = payoff_matrix_from_tau_matrix(get_zoo(zoo_key).load(), zoo=zoo_key)
    bot_names = list(payoff.bots)
    suspect = suspect_cells_for(payoff)

    r = enumerate_pure_ess(bot_names, payoff.A)
    r = flag_suspect_cells(r, suspect)

    n = len(bot_names)
    assert len(r.pairwise) == n * (n - 1)

    # CooperateBot is strictly invaded by DefectBot under b > c > 0 — this is
    # forced by the payoff convention, not by any particular zoo.
    coop = _summary(r, "CooperateBot")
    assert not coop.is_ESS
    assert "DefectBot" in coop.failing_invaders

    # Every stipulated (unproven) off-diagonal cell is flagged in both
    # orientations. `flag_suspect_cells` also flags a row when the DIAGONAL
    # cell of either endpoint is stipulated, so this is containment, not
    # equality.
    flagged = {(p.i, p.j) for p in r.pairwise if p.touches_suspect_cell}
    assert {(i, j) for i, j in suspect if i != j} <= flagged

    # Only bots that appear in a stipulated cell carry the dependency note.
    involved = {b for pair in suspect for b in pair}
    notes_by_type = {s.type: s.notes for s in r.summary}
    for name in bot_names:
        if name not in involved:
            assert notes_by_type[name] == ""

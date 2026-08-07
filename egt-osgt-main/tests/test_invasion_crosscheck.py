"""Tests for src/invasion/cross_check.py — clause-(a) vs ESS comparison."""

from __future__ import annotations

import csv
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

import numpy as np

from src.invasion.analysis import compute_readouts
from src.invasion.cross_check import compare_against_ess
from src.invasion.graph import build_strict, build_weak


def _write_ess_summary(path: Path, rows):
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["type", "is_ESS", "n_invaders", "failing_invaders", "notes"])
        for r in rows:
            w.writerow(r)


def test_tie_flips_clause_a_candidate(tmp_path):
    """Vertex 0 has in_degree(G_strict)=0 (candidate by clause (a)) but ESS
    rejects it because vertex 1 ties at column 0 with A[0,1]<=A[1,1].
    """
    names = ["v0", "v1", "v2"]
    A = np.array([
        [2.0, 0.0, 0.0],
        [2.0, 2.0, 0.0],     # A[1,0]=2 == A[0,0]=2 → tie at (1,0)
        [0.0, 0.0, 2.0],
    ])
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)
    # Strict edges: A[i,j] > A[j,j].
    # A[0,1]=0 vs A[1,1]=2 → no 0->1
    # A[0,2]=0 vs A[2,2]=2 → no 0->2
    # A[1,0]=2 vs A[0,0]=2 → tie only, no strict
    # A[1,2]=0 vs A[2,2]=2 → no
    # A[2,0]=0 vs A[0,0]=2 → no
    # A[2,1]=0 vs A[1,1]=2 → no
    assert list(G_s.edges) == []
    assert G_s.in_degree(0) == 0

    ess_path = tmp_path / "ess_summary.csv"
    # Hand-written ESS verdict: v0 is NOT an ESS (because clause-(b) fails
    # at the v1 tie: A[0,1]=0 <= A[1,1]=2). v1, v2 likewise not ESS.
    _write_ess_summary(ess_path, [
        ("v0", "False", 1, "v1", ""),
        ("v1", "False", 0, "", ""),
        ("v2", "False", 0, "", ""),
    ])

    agreements = compare_against_ess(G_s, G_w, ess_path)
    a0 = next(a for a in agreements if a.name == "v0")
    assert a0.candidate_ESS_by_clause_a is True
    assert a0.is_ESS_per_ess_summary is False
    assert a0.agrees_with_ess is False
    # v1 ties INTO v0 (column-0 tie).
    assert ("v1", "v0") in a0.responsible_ties


def test_perfect_agreement(tmp_path):
    """Coordination 2x2: both vertices are isolated → clause-(a) candidates.
    If the hand-written ESS summary marks both as ESS, no disagreements.
    """
    names = ["A", "B"]
    A = np.array([[1.0, 0.0], [0.0, 1.0]])
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)

    ess_path = tmp_path / "ess_summary.csv"
    _write_ess_summary(ess_path, [
        ("A", "True", 0, "", ""),
        ("B", "True", 0, "", ""),
    ])

    agreements = compare_against_ess(G_s, G_w, ess_path)
    for a in agreements:
        assert a.candidate_ESS_by_clause_a is True
        assert a.is_ESS_per_ess_summary is True
        assert a.agrees_with_ess is True


def test_missing_ess_file_is_handled(tmp_path):
    names = ["x"]
    A = np.array([[0.0]])
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)
    agreements = compare_against_ess(G_s, G_w, None)
    assert len(agreements) == 1
    assert agreements[0].is_ESS_per_ess_summary is None
    assert agreements[0].agrees_with_ess is None

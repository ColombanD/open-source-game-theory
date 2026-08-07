"""Tests for src/invasion/graph.py — graph construction and attributes."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

import numpy as np
import pytest

from src.invasion.graph import (
    SUSPECT_CELLS, build_strict, build_weak, tie_edges,
)


def test_all_defect_1x1_isolated():
    names = ["X"]
    A = np.array([[0.0]])
    G = build_strict(names, A)
    assert list(G.nodes) == [0]
    assert list(G.edges) == []
    assert G.nodes[0]["in_deg"] == 0 and G.nodes[0]["out_deg"] == 0


def test_all_defect_2x2_no_strict_edges_all_ties():
    names = ["X", "Y"]
    A = np.zeros((2, 2))
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)
    assert list(G_s.edges) == []
    # G_weak should contain both directions as ties.
    edges = set(G_w.edges)
    assert edges == {(0, 1), (1, 0)}
    for u, v, d in G_w.edges(data=True):
        assert d["is_tie"] is True
        assert d["margin"] == 0.0


def test_rock_paper_scissors():
    names = ["R", "P", "S"]
    A = np.array([[0, -1, 1],
                  [1, 0, -1],
                  [-1, 1, 0]], dtype=float)
    G = build_strict(names, A)
    # Strict edges: R->P, P->S, S->R   (because A[R,P]=-1<0=A[P,P] is wrong;
    # recompute: i->j iff A[i,j] > A[j,j]; A[j,j]=0 for all j; A[i,j]>0 holds
    # for (R,S), (P,R), (S,P). So R->S, P->R, S->P.)
    expected = {(0, 2), (1, 0), (2, 1)}
    assert set(G.edges) == expected
    # No in-degree-zero vertex.
    assert all(G.in_degree(v) > 0 for v in G.nodes)


def test_hawk_dove_two_cycle():
    # Hawk-Dove with V=2, C=4: A = [[(V-C)/2, V],[0, V/2]] = [[-1, 2],[0, 1]]
    names = ["Hawk", "Dove"]
    A = np.array([[-1.0, 2.0], [0.0, 1.0]])
    G = build_strict(names, A)
    # Hawk->Dove: A[H,D]=2 > A[D,D]=1   ✓
    # Dove->Hawk: A[D,H]=0 > A[H,H]=-1  ✓
    assert set(G.edges) == {(0, 1), (1, 0)}
    assert G.in_degree(0) > 0 and G.in_degree(1) > 0


def test_coordination_2x2_two_isolates():
    names = ["A", "B"]
    A = np.array([[1.0, 0.0], [0.0, 1.0]])
    G = build_strict(names, A)
    # A[0,1]=0 vs A[1,1]=1 → no edge 0->1
    # A[1,0]=0 vs A[0,0]=1 → no edge 1->0
    assert list(G.edges) == []
    assert all(G.in_degree(v) == 0 and G.out_degree(v) == 0 for v in G.nodes)


def test_strict_subset_of_weak():
    rng = np.random.default_rng(7)
    A = rng.normal(size=(6, 6))
    names = [f"v{i}" for i in range(6)]
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)
    assert set(G_s.edges) <= set(G_w.edges)


def test_tie_attribute_separates_strict_and_tied():
    names = ["a", "b", "c"]
    # Constructed so margin == 0 exactly for one edge.
    A = np.array([
        [2.0, 0.0, 0.0],
        [2.0, 2.0, 0.0],   # A[1,0]=2 == A[0,0]=2 → tie at (1, 0)
        [0.0, 0.0, 2.0],
    ])
    G_s = build_strict(names, A)
    G_w = build_weak(names, A)
    assert (1, 0) not in G_s.edges
    assert (1, 0) in G_w.edges
    assert G_w.edges[1, 0]["is_tie"] is True
    assert (1, 0) in tie_edges(G_w)


def test_suspect_flag_on_red_cell_edges():
    names = ["CupodBot", "DupocBot", "Other"]
    # Build a matrix where (CupodBot, DupocBot) yields a strict edge.
    A = np.array([
        [1.0, 5.0, 0.0],   # A[Cupod, Dupoc] = 5 > A[Dupoc, Dupoc]=2  ✓
        [0.0, 2.0, 0.0],
        [0.0, 0.0, 1.0],
    ])
    G = build_strict(names, A, suspect_cells=SUSPECT_CELLS)
    assert G.edges[0, 1]["touches_suspect_cell"] is True


def test_diagonal_non_finite_raises():
    names = ["X", "Y"]
    A = np.array([[np.nan, 0.0], [0.0, 0.0]])
    with pytest.raises(ValueError, match="diagonal"):
        build_strict(names, A)


def test_shape_mismatch_raises():
    with pytest.raises(ValueError, match="square"):
        build_strict(["X"], np.zeros((2, 2)))

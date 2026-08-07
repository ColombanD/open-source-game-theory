"""Tests for src/invasion/analysis.py — SCCs, cycles, roles, condensation."""

from __future__ import annotations

import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

import numpy as np
import networkx as nx

from src.invasion.analysis import compute_readouts
from src.invasion.graph import build_strict, build_weak


def _build(names, A):
    return (build_strict(names, A), build_weak(names, A))


def test_rps_one_scc_size_3_one_cycle():
    names = ["R", "P", "S"]
    A = np.array([[0, -1, 1], [1, 0, -1], [-1, 1, 0]], dtype=float)
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    assert len(res.sccs) == 1
    assert res.sccs[0].size == 3
    assert set(res.sccs[0].members) == {0, 1, 2}
    assert all(res.roles[v] == "in_cycle" for v in range(3))
    assert res.cycles.n_cycles_total == 1
    assert len(res.cycles.by_length[3]) == 1
    assert res.cycles.two_cycles == []


def test_hawk_dove_one_two_cycle():
    names = ["Hawk", "Dove"]
    A = np.array([[-1.0, 2.0], [0.0, 1.0]])
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    # One SCC of size 2.
    assert len(res.sccs) == 1
    assert res.sccs[0].size == 2
    # One two-cycle.
    assert len(res.cycles.two_cycles) == 1
    # Both vertices role == in_cycle.
    assert all(res.roles[v] == "in_cycle" for v in range(2))


def test_coordination_two_isolates_two_singleton_sccs():
    names = ["A", "B"]
    A = np.array([[1.0, 0.0], [0.0, 1.0]])
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    assert len(res.sccs) == 2
    assert all(s.size == 1 for s in res.sccs)
    assert all(res.roles[v] == "isolated" for v in range(2))
    assert res.cycles.n_cycles_total == 0
    assert res.isolated == [0, 1]


def test_role_clause_a_candidate():
    names = ["a", "b"]
    # a beats b, b does not beat a, neither sits in a cycle, neither is isolated.
    # a: in=0, out=1   → clause_a_candidate
    # b: in=1, out=0   → impotent
    A = np.array([[1.0, 2.0],
                  [0.0, 1.0]])    # A[a,b]=2 > A[b,b]=1 → a->b;
                                  # A[b,a]=0 < A[a,a]=1 → no b->a
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    assert res.roles[0] == "clause_a_candidate"
    assert res.roles[1] == "impotent"


def test_terminal_scc_detection():
    # Linear: 0 -> 1, 1 -> 2. Three singleton SCCs; the terminal one is {2}.
    names = ["a", "b", "c"]
    # Engineer payoffs so the strict graph is 0->1, 1->2 only.
    # i->j iff A[i,j] > A[j,j].
    # 0->1: A[0,1] > A[1,1]
    # 1->2: A[1,2] > A[2,2]
    # NOT 1->0, 2->1, 2->0, 0->2.
    A = np.array([
        [5.0, 6.0, 0.0],   # A[0,1]=6 > 5=A[1,1] ✓; A[0,2]=0 < 1=A[2,2] ✗
        [0.0, 5.0, 2.0],   # A[1,0]=0 < 5 ✗; A[1,2]=2 > 1=A[2,2] ✓
        [0.0, 0.0, 1.0],   # A[2,0]=0 < 5 ✗; A[2,1]=0 < 5 ✗
    ])
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    assert set(G_s.edges) == {(0, 1), (1, 2)}
    assert len(res.sccs) == 3
    # The vertex 2 is the unique sink.
    sid_of_2 = res.scc_of[2]
    assert sid_of_2 in res.terminal_sccs
    # And 0 (the source) should NOT be terminal.
    assert res.scc_of[0] not in res.terminal_sccs


def test_cycle_cap_hit():
    # Complete digraph K_4 — has many simple cycles. With cap=2 we'll hit it.
    G = nx.complete_graph(4, create_using=nx.DiGraph)
    G_w = G.copy()
    for u, v in G.edges:
        G.edges[u, v]["margin"] = 1.0
        G.edges[u, v]["is_tie"] = False
        G.edges[u, v]["touches_suspect_cell"] = False
        G_w.edges[u, v]["margin"] = 1.0
        G_w.edges[u, v]["is_tie"] = False
        G_w.edges[u, v]["touches_suspect_cell"] = False
    for v in G.nodes:
        G.nodes[v]["name"] = f"v{v}"
        G.nodes[v]["in_deg"] = int(G.in_degree(v))
        G.nodes[v]["out_deg"] = int(G.out_degree(v))
        G_w.nodes[v]["name"] = f"v{v}"
    res = compute_readouts(G, G_w, cycle_cap=2)
    assert res.cycles.cap_hit is True
    # Fallback should give at least the 2-cycles.
    assert res.cycles.length_bound_if_capped is not None


def test_condensation_topological_order_makes_sense():
    names = ["a", "b", "c"]
    A = np.array([
        [5.0, 6.0, 0.0],
        [0.0, 5.0, 2.0],
        [0.0, 0.0, 1.0],
    ])
    G_s, G_w = _build(names, A)
    res = compute_readouts(G_s, G_w)
    # topological order is over scc ids — check it respects the SCC adjacency.
    pos = {sid: i for i, sid in enumerate(res.topological_order)}
    for u, v in res.condensation.edges:
        assert pos[u] < pos[v]


def test_isolated_role_ordering_beats_in_cycle_for_singleton():
    # A 2x2 matrix with no edges either way → two isolated singleton SCCs;
    # role should be "isolated", not "clause_a_candidate".
    A = np.array([[5.0, 0.0], [0.0, 5.0]])
    G_s, G_w = _build(["a", "b"], A)
    res = compute_readouts(G_s, G_w)
    for v in range(2):
        assert res.roles[v] == "isolated"

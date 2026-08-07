"""Build the strict and weak invasion graphs as `networkx.DiGraph`.

Both graphs carry the full vertex set (so isolates persist) and the
following edge attributes:

  G>.edges[i, j]:
      margin                = A[i, j] - A[j, j]   (> 0)
      is_tie                = False
      touches_suspect_cell  = bool

  G>=.edges[i, j]:
      margin                = A[i, j] - A[j, j]   (>= 0; tie iff == 0)
      is_tie                = (margin == 0)
      touches_suspect_cell  = bool

Node attributes set at construction time:
      name      = bot_names[i]
      in_deg    = G_strict.in_degree(i)            (populated post-build)
      out_deg   = G_strict.out_degree(i)           (populated post-build)
      scc_id    = int                              (filled by analysis)
      role      = str                              (filled by analysis)
"""

from __future__ import annotations

from typing import Iterable, List, Set, Tuple

import networkx as nx  # type: ignore
import numpy as np  # type: ignore


SUSPECT_CELLS: Tuple[Tuple[str, str], ...] = (
    ("CupodBot", "DupocBot"),
    ("DupocBot", "CupodBot"),
)


def _check_inputs(names: List[str], A: np.ndarray) -> None:
    n = len(names)
    if n == 0:
        raise ValueError("invasion graph requires at least one type")
    if A.shape != (n, n):
        raise ValueError(f"A must be square of shape ({n}, {n}); got {A.shape}")
    if not np.all(np.isfinite(np.diag(A))):
        bad = [names[i] for i in range(n) if not np.isfinite(A[i, i])]
        raise ValueError(
            "diagonal of A must be finite (invasion test references A[j,j]); "
            f"undefined diagonal entries for: {bad}"
        )
    if not np.all(np.isfinite(A)):
        bad = [
            (names[i], names[j])
            for i in range(n) for j in range(n)
            if not np.isfinite(A[i, j])
        ]
        raise ValueError(
            f"A must contain only finite values; undefined cells: {bad}"
        )


def _touches(i: str, j: str, suspect_set: Set[Tuple[str, str]]) -> bool:
    return (i, j) in suspect_set or (j, i) in suspect_set


def build_strict(
    names: List[str],
    A: np.ndarray,
    suspect_cells: Iterable[Tuple[str, str]] = SUSPECT_CELLS,
    atol: float = 1e-12,
) -> nx.DiGraph:
    """Build the strict invasion graph G> on indices 0..N-1."""
    _check_inputs(names, A)
    suspect_set = {tuple(p) for p in suspect_cells}
    n = len(names)

    G = nx.DiGraph()
    for i in range(n):
        G.add_node(i, name=names[i])

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            margin = float(A[i, j] - A[j, j])
            if margin > atol:
                G.add_edge(
                    i, j,
                    margin=margin,
                    is_tie=False,
                    touches_suspect_cell=_touches(names[i], names[j], suspect_set),
                )

    for i in range(n):
        G.nodes[i]["in_deg"] = int(G.in_degree(i))
        G.nodes[i]["out_deg"] = int(G.out_degree(i))

    return G


def build_weak(
    names: List[str],
    A: np.ndarray,
    suspect_cells: Iterable[Tuple[str, str]] = SUSPECT_CELLS,
    atol: float = 1e-12,
) -> nx.DiGraph:
    """Build the weak invasion graph G>= on indices 0..N-1.

    The edge set is a superset of `build_strict(names, A).edges`; the
    additional edges are exactly the tied pairs (margin == 0 within atol).
    """
    _check_inputs(names, A)
    suspect_set = {tuple(p) for p in suspect_cells}
    n = len(names)

    G = nx.DiGraph()
    for i in range(n):
        G.add_node(i, name=names[i])

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            margin = float(A[i, j] - A[j, j])
            if margin >= -atol:
                is_tie = abs(margin) <= atol
                G.add_edge(
                    i, j,
                    margin=margin,
                    is_tie=is_tie,
                    touches_suspect_cell=_touches(names[i], names[j], suspect_set),
                )

    for i in range(n):
        G.nodes[i]["in_deg"] = int(G.in_degree(i))
        G.nodes[i]["out_deg"] = int(G.out_degree(i))

    return G


def tie_edges(G_weak: nx.DiGraph) -> List[Tuple[int, int]]:
    """Edges in G_weak whose `is_tie` flag is True. Equals E(G>=) \\ E(G>)."""
    return [(u, v) for u, v, d in G_weak.edges(data=True) if d["is_tie"]]

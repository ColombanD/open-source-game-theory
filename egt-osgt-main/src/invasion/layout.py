"""Layout strategies for the invasion-graph visualisation.

Priority:
    1. nx.nx_agraph.graphviz_layout(prog="dot")   (preferred)
    2. nx.nx_pydot.graphviz_layout(prog="dot")
    3. manual layered layout from the condensation DAG
    4. nx.spring_layout(seed=...)                  (last resort)
"""

from __future__ import annotations

from typing import Dict, List, Optional, Tuple

import networkx as nx  # type: ignore


def _agraph_layout(G: nx.DiGraph) -> Optional[Dict[int, Tuple[float, float]]]:
    try:
        return nx.nx_agraph.graphviz_layout(G, prog="dot")
    except Exception:
        return None


def _pydot_layout(G: nx.DiGraph) -> Optional[Dict[int, Tuple[float, float]]]:
    try:
        return nx.nx_pydot.graphviz_layout(G, prog="dot")
    except Exception:
        return None


def _manual_layered_layout(
    G_strict: nx.DiGraph,
    condensation: nx.DiGraph,
    topological_order: List[int],
    bot_names: List[str],
    layer_w: float = 3.0,
    node_h: float = 1.2,
    intra_scc_x_jitter: float = 0.4,
) -> Dict[int, Tuple[float, float]]:
    """Place each SCC at a layer x = topological index; vertices within an
    SCC are spread vertically, sorted by name for determinism. Members of
    a non-singleton SCC also get a small horizontal jitter so the
    enclosing box has visible area.
    """
    layer = {scc_id: idx for idx, scc_id in enumerate(topological_order)}
    pos: Dict[int, Tuple[float, float]] = {}
    for scc_id in topological_order:
        members = sorted(
            condensation.nodes[scc_id]["members"],
            key=lambda v: bot_names[v],
        )
        base_x = layer[scc_id] * layer_w
        n = len(members)
        for k, v in enumerate(members):
            y = (k - (n - 1) / 2.0) * node_h
            # Stagger x within an SCC so 2-cycles draw cleanly.
            jitter = (k - (n - 1) / 2.0) * intra_scc_x_jitter if n > 1 else 0.0
            pos[v] = (base_x + jitter, y)
    return pos


def compute_layout(
    G_strict: nx.DiGraph,
    condensation: nx.DiGraph,
    topological_order: List[int],
    bot_names: List[str],
    seed: int = 20260514,
) -> Tuple[Dict[int, Tuple[float, float]], str]:
    """Return (pos, backend_name)."""
    pos = _agraph_layout(G_strict)
    if pos is not None:
        return pos, "graphviz_agraph_dot"
    pos = _pydot_layout(G_strict)
    if pos is not None:
        return pos, "graphviz_pydot_dot"
    try:
        return (
            _manual_layered_layout(
                G_strict, condensation, topological_order, bot_names
            ),
            "manual_layered",
        )
    except Exception:
        return (
            nx.spring_layout(G_strict, seed=seed),
            "spring_fallback",
        )


def compute_condensation_layout(
    condensation: nx.DiGraph,
    seed: int = 20260514,
) -> Tuple[Dict[int, Tuple[float, float]], str]:
    """Layout for the SCC-condensation DAG."""
    pos = _agraph_layout(condensation)
    if pos is not None:
        return pos, "graphviz_agraph_dot"
    pos = _pydot_layout(condensation)
    if pos is not None:
        return pos, "graphviz_pydot_dot"

    # Manual layered: x = topo index, y = stable per-SCC offset.
    topo = list(nx.topological_sort(condensation))
    layer = {sid: i for i, sid in enumerate(topo)}
    # Group SCCs at the same x and spread them vertically.
    by_layer: Dict[int, List[int]] = {}
    for sid, x in layer.items():
        by_layer.setdefault(x, []).append(sid)
    pos = {}
    for x, sids in by_layer.items():
        for k, sid in enumerate(sorted(sids)):
            pos[sid] = (x * 3.0, (k - (len(sids) - 1) / 2.0) * 1.5)
    return pos, "manual_layered"

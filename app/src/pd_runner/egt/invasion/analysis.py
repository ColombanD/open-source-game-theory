"""SCC / condensation / cycle / role analysis on the invasion graph."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Iterator, List, Optional, Tuple

import networkx as nx  # type: ignore


@dataclass
class SCCRecord:
    scc_id: int
    members: List[int]              # original-vertex indices
    member_names: List[str]
    size: int
    is_terminal: bool
    in_neighbors: List[int]         # other scc_ids
    out_neighbors: List[int]


@dataclass
class CycleReport:
    cap: int
    cap_hit: bool
    length_bound_if_capped: Optional[int]
    n_cycles_total: int
    by_length: Dict[int, List[List[int]]]   # length -> list of cycles (vertex index lists)
    two_cycles: List[Tuple[int, int]]       # unordered (u, v) pairs as ordered with u < v


@dataclass
class AnalysisResult:
    in_deg: Dict[int, int]
    out_deg: Dict[int, int]
    isolated: List[int]
    sccs: List[SCCRecord]
    scc_of: Dict[int, int]
    condensation: nx.DiGraph                 # nodes = scc_ids, edges = condensation edges
    topological_order: List[int]             # scc_ids in topo order
    terminal_sccs: List[int]                 # scc_ids with cond.out_degree == 0
    cycles: CycleReport
    roles: Dict[int, str]


def _simple_cycles_capped(
    G: nx.DiGraph, cap: int
) -> Tuple[List[List[int]], bool, Optional[int]]:
    """Enumerate simple cycles up to `cap`. If hit, re-enumerate with a
    length bound so the report is at least complete for short cycles.

    Returns (cycles, cap_hit, length_bound_if_capped).
    """
    raw: List[List[int]] = []
    cap_hit = False
    for k, cyc in enumerate(nx.simple_cycles(G)):
        if k >= cap:
            cap_hit = True
            break
        raw.append(list(cyc))
    if not cap_hit:
        return raw, False, None

    # Fallback: enumerate by length, stop at the largest L whose cycle
    # set still fits inside the cap. If even the L=2 set is bigger than
    # the cap, take that set anyway — the spec asks for *some* bounded
    # report — and mark the bound as 2 so the truncation is visible.
    max_len = 0
    bounded: List[List[int]] = []
    for L in range(2, G.number_of_nodes() + 1):
        chunk = list(nx.simple_cycles(G, length_bound=L))
        if len(chunk) <= cap:
            bounded = chunk
            max_len = L
        else:
            break
    if max_len == 0:
        bounded = list(nx.simple_cycles(G, length_bound=2))
        max_len = 2
    return bounded, True, max_len


def assign_roles(
    G_strict: nx.DiGraph,
    scc_of: Dict[int, int],
    scc_size: Dict[int, int],
) -> Dict[int, str]:
    """Tag every vertex with one of:
        "isolated", "in_cycle", "clause_a_candidate", "impotent", "transient".

    Ordering matters: isolated > in_cycle > clause_a_candidate > impotent > transient.
    """
    roles: Dict[int, str] = {}
    for v in G_strict.nodes:
        indeg = G_strict.in_degree(v)
        outdeg = G_strict.out_degree(v)
        if indeg == 0 and outdeg == 0:
            role = "isolated"
        elif scc_size[scc_of[v]] > 1:
            role = "in_cycle"
        elif indeg == 0:
            role = "clause_a_candidate"
        elif outdeg == 0:
            role = "impotent"
        else:
            role = "transient"
        roles[v] = role
        G_strict.nodes[v]["role"] = role
    return roles


def compute_readouts(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    cycle_cap: int = 10_000,
) -> AnalysisResult:
    """Compute SCCs, condensation, simple cycles, and roles."""
    if not (set(G_strict.edges) <= set(G_weak.edges)):
        raise ValueError("E(G_strict) must be a subset of E(G_weak)")

    in_deg = {v: int(G_strict.in_degree(v)) for v in G_strict.nodes}
    out_deg = {v: int(G_strict.out_degree(v)) for v in G_strict.nodes}
    isolated = list(nx.isolates(G_strict))

    # SCCs: produce a stable ordering by min-member-index so scc_id is reproducible.
    scc_sets = [frozenset(s) for s in nx.strongly_connected_components(G_strict)]
    scc_sets.sort(key=lambda s: min(s))

    # Use the sorted scc list as the canonical decomposition for condensation.
    cond = nx.condensation(G_strict, scc=scc_sets)

    scc_of: Dict[int, int] = {}
    for scc_id, members in enumerate(scc_sets):
        for v in members:
            scc_of[v] = scc_id

    topo_order = list(nx.topological_sort(cond))
    terminal_sccs = [sid for sid in cond.nodes if cond.out_degree(sid) == 0]

    sccs: List[SCCRecord] = []
    for sid in range(len(scc_sets)):
        members_sorted = sorted(scc_sets[sid])
        sccs.append(
            SCCRecord(
                scc_id=sid,
                members=members_sorted,
                member_names=[G_strict.nodes[v]["name"] for v in members_sorted],
                size=len(members_sorted),
                is_terminal=(cond.out_degree(sid) == 0),
                in_neighbors=sorted(cond.predecessors(sid)),
                out_neighbors=sorted(cond.successors(sid)),
            )
        )

    raw_cycles, cap_hit, length_bound = _simple_cycles_capped(G_strict, cycle_cap)
    by_length: Dict[int, List[List[int]]] = {}
    for cyc in raw_cycles:
        by_length.setdefault(len(cyc), []).append(cyc)
    for L in by_length:
        by_length[L].sort(key=lambda c: tuple(c))

    two_cycles = sorted(
        {tuple(sorted((u, v)))
         for u, v in G_strict.edges if G_strict.has_edge(v, u)}
    )

    scc_size = {sid: len(scc_sets[sid]) for sid in range(len(scc_sets))}
    roles = assign_roles(G_strict, scc_of, scc_size)

    return AnalysisResult(
        in_deg=in_deg,
        out_deg=out_deg,
        isolated=sorted(isolated),
        sccs=sccs,
        scc_of=scc_of,
        condensation=cond,
        topological_order=topo_order,
        terminal_sccs=sorted(terminal_sccs),
        cycles=CycleReport(
            cap=cycle_cap,
            cap_hit=cap_hit,
            length_bound_if_capped=length_bound,
            n_cycles_total=len(raw_cycles),
            by_length=by_length,
            two_cycles=[tuple(t) for t in two_cycles],
        ),
        roles=roles,
    )

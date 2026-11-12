"""Classify extreme NE by symmetry and group them into Nash components.

Symmetric NE:  xi == eta.
Asymmetric NE: xi != eta. Every asymmetric NE (xi, eta) of a symmetric
              bimatrix game (A, A^T) is paired with (eta, xi), which is
              also an NE. We assign matched pairs a shared id.

Nash components are the connected components of the equilibrium set. That set
is the union of conv(X) x conv(Y) over the maximal bicliques X x Y of the
bipartite graph whose nodes are the row strategies and the column strategies of
the extreme NE, with one edge per extreme NE (Avis, Rosenberg, Savani and von
Stengel 2010; Jansen 1981). Two extreme NE therefore lie in one component iff a
path of that graph joins them, i.e. iff a chain of extreme NE links them, each
sharing its row strategy or its column strategy with the next.

Until 2026-11-10 the grouping tested whether the MIDPOINT of two extreme NE is
an NE. That is not sufficient: the midpoint can be a separate equilibrium. In
the coordination game A = I, (e1, e1) and (e2, e2) are isolated, yet their
midpoint is the third, mixed equilibrium, so the test reported two components
where there are three.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from pd_runner.egt.nash.reconcile import ReconciledNE


@dataclass
class ClassifiedNE:
    ne_index: int
    classification: str                 # "symmetric" | "asymmetric"
    asymmetric_pair_id: Optional[int]
    component_id: int


def classify_symmetry(merged: List[ReconciledNE]) -> Dict[int, Tuple[str, Optional[int]]]:
    """Assign each NE 'symmetric' or 'asymmetric'; match asymmetric pairs by swap."""
    out: Dict[int, Tuple[str, Optional[int]]] = {}
    swap_to_idx: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], int] = {}
    pair_counter = 0

    for idx, ne in enumerate(merged):
        if ne.xi == ne.eta:
            out[idx] = ("symmetric", None)
            continue
        key = (ne.eta, ne.xi)
        if key in swap_to_idx:
            partner = swap_to_idx[key]
            # partner was set as asymmetric-no-id previously; assign a pair id now.
            if out[partner][1] is None:
                out[partner] = ("asymmetric", pair_counter)
                out[idx] = ("asymmetric", pair_counter)
                pair_counter += 1
            else:
                out[idx] = ("asymmetric", out[partner][1])
        else:
            out[idx] = ("asymmetric", None)
            swap_to_idx[(ne.xi, ne.eta)] = idx

    return out


def group_components(
    A: List[List[Fraction]],
    merged: List[ReconciledNE],
) -> List[int]:
    """Return component id for each extreme NE.

    The connected components of the bipartite graph on (row strategies, column
    strategies) with one edge per extreme NE: two extreme NE are in the same
    component iff a chain of extreme NE joins them, consecutive ones sharing
    their `xi` or their `eta`. `A` is not needed (the extreme NE determine the
    components) and is kept for the call signature.
    """
    parent: Dict[Tuple[str, Tuple[Fraction, ...]], Tuple[str, Tuple[Fraction, ...]]] = {}

    def find(node: Tuple[str, Tuple[Fraction, ...]]) -> Tuple[str, Tuple[Fraction, ...]]:
        parent.setdefault(node, node)
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    for ne in merged:
        parent[find(("row", tuple(ne.xi)))] = find(("col", tuple(ne.eta)))

    # Renumber so component IDs are 0..K-1 in first-occurrence order.
    relabel: Dict[Tuple[str, Tuple[Fraction, ...]], int] = {}
    return [
        relabel.setdefault(find(("row", tuple(ne.xi))), len(relabel))
        for ne in merged
    ]


def classify_all(
    A: List[List[Fraction]],
    merged: List[ReconciledNE],
) -> List[ClassifiedNE]:
    """Full classification: symmetry + component grouping."""
    sym = classify_symmetry(merged)
    comp = group_components(A, merged)
    out: List[ClassifiedNE] = []
    for idx in range(len(merged)):
        classification, pair_id = sym[idx]
        out.append(
            ClassifiedNE(
                ne_index=idx,
                classification=classification,
                asymmetric_pair_id=pair_id,
                component_id=comp[idx],
            )
        )
    return out


def component_summary(
    classified: List[ClassifiedNE],
) -> List[Dict[str, object]]:
    """Group extreme NE into one record per component."""
    by_id: Dict[int, List[int]] = {}
    for c in classified:
        by_id.setdefault(c.component_id, []).append(c.ne_index)
    out: List[Dict[str, object]] = []
    for comp_id in sorted(by_id):
        members = by_id[comp_id]
        is_symmetric_component = all(
            classified[i].classification == "symmetric" for i in members
        )
        out.append({
            "id": comp_id,
            "extreme_NE_indices": members,
            "size": len(members),
            "is_symmetric_component": is_symmetric_component,
        })
    return out

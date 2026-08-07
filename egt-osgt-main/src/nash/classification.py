"""Classify extreme NE by symmetry and group them into Nash components.

Symmetric NE:  xi == eta.
Asymmetric NE: xi != eta. Every asymmetric NE (xi, eta) of a symmetric
              bimatrix game (A, A^T) is paired with (eta, xi), which is
              also an NE. We assign matched pairs a shared id.

Nash components are connected sets of NE. We group extreme NE into
components by repeatedly testing midpoint NE-ness on the original A:
two extreme NE are in the same component iff their midpoint (and hence
the whole connecting segment, by convexity of the NE set on a face) is
also an NE.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from src.nash.reconcile import ReconciledNE


@dataclass
class ClassifiedNE:
    ne_index: int
    classification: str                 # "symmetric" | "asymmetric"
    asymmetric_pair_id: Optional[int]
    component_id: int


def _is_ne(
    A: List[List[Fraction]],
    xi: Tuple[Fraction, ...],
    eta: Tuple[Fraction, ...],
) -> bool:
    """Exact test: is (xi, eta) a NE of the bimatrix (A, A^T)?

    Row's BR vector: (A eta)[i] = sum_j A[i,j] eta[j].
    Col's BR vector: (Axi_col)[j] = sum_i A[j,i] xi[i] (B = A^T).
    """
    n = len(A)
    A_eta = [sum(A[i][j] * eta[j] for j in range(n)) for i in range(n)]
    u = sum(xi[i] * A_eta[i] for i in range(n))
    if any(A_eta[i] > u for i in range(n)):
        return False
    if any(xi[i] > 0 and A_eta[i] != u for i in range(n)):
        return False
    Axi_col = [sum(A[j][i] * xi[i] for i in range(n)) for j in range(n)]
    v = sum(eta[j] * Axi_col[j] for j in range(n))
    if any(Axi_col[j] > v for j in range(n)):
        return False
    if any(eta[j] > 0 and Axi_col[j] != v for j in range(n)):
        return False
    return True


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

    Two extreme NE i, j are in the same component iff
    (xi_avg, eta_avg) = ((xi_i + xi_j)/2, (eta_i + eta_j)/2) is itself an NE.
    Components are then the connected components of this relation.
    """
    n = len(merged)
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        rx, ry = find(x), find(y)
        if rx != ry:
            parent[ry] = rx

    half = Fraction(1, 2)
    for i in range(n):
        for j in range(i + 1, n):
            if find(i) == find(j):
                continue
            xi_avg = tuple(half * (merged[i].xi[k] + merged[j].xi[k]) for k in range(len(merged[i].xi)))
            eta_avg = tuple(half * (merged[i].eta[k] + merged[j].eta[k]) for k in range(len(merged[i].eta)))
            if _is_ne(A, xi_avg, eta_avg):
                union(i, j)

    # Renumber so component IDs are 0..K-1 in first-occurrence order.
    relabel: Dict[int, int] = {}
    out: List[int] = []
    next_id = 0
    for i in range(n):
        root = find(i)
        if root not in relabel:
            relabel[root] = next_id
            next_id += 1
        out.append(relabel[root])
    return out


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

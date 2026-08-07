"""Cross-check the invasion graph against an existing ESS verdict file.

The strict invasion graph encodes only clause (a) of Maynard-Smith ESS:
    in_degree(v, G_strict) == 0   <=>   for all j != v, A[v, v] >= A[j, v].

This is a NECESSARY condition for v to be an ESS, but not sufficient:
clause (b) may still fail at a tied invader. So every pure ESS is
in-degree-zero, and the disagreements are always shaped as

    candidate_ESS_by_clause_a = True   AND   is_ESS_per_ess_summary = False.

For each disagreement we list the column-v ties (i.e. weak invaders into
v that are not strict invaders) that the ESS pipeline rejected.
"""

from __future__ import annotations

import csv
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple

import networkx as nx  # type: ignore


@dataclass
class VertexAgreement:
    name: str
    candidate_ESS_by_clause_a: bool
    is_ESS_per_ess_summary: Optional[bool]
    agrees_with_ess: Optional[bool]
    responsible_ties: List[Tuple[str, str]]   # list of (invader_name, v_name)


def _read_ess_summary(path: Path) -> Dict[str, bool]:
    out: Dict[str, bool] = {}
    with open(path, newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            out[row["type"]] = (row["is_ESS"].strip().lower() == "true")
    return out


def compare_against_ess(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    ess_summary_path: Optional[Path],
) -> List[VertexAgreement]:
    """For every vertex, build a VertexAgreement record.

    If `ess_summary_path` is None or missing, `is_ESS_per_ess_summary`
    and `agrees_with_ess` are returned as None; `responsible_ties` is
    still populated.
    """
    ess: Optional[Dict[str, bool]] = None
    if ess_summary_path is not None and Path(ess_summary_path).exists():
        ess = _read_ess_summary(Path(ess_summary_path))

    # Tie set: edges in weak but not strict, by (invader, victim) names.
    tie_set: List[Tuple[str, str]] = []
    for u, v, d in G_weak.edges(data=True):
        if d["is_tie"]:
            tie_set.append((G_weak.nodes[u]["name"], G_weak.nodes[v]["name"]))

    out: List[VertexAgreement] = []
    for v in G_strict.nodes:
        name = G_strict.nodes[v]["name"]
        candidate = (G_strict.in_degree(v) == 0)
        is_ess = ess.get(name) if ess is not None else None
        agrees = None if is_ess is None else (candidate == is_ess)
        # Column-v ties: invaders weakly tying into v.
        responsible = [(inv, vic) for (inv, vic) in tie_set if vic == name]
        out.append(
            VertexAgreement(
                name=name,
                candidate_ESS_by_clause_a=candidate,
                is_ESS_per_ess_summary=is_ess,
                agrees_with_ess=agrees,
                responsible_ties=responsible,
            )
        )
    return out

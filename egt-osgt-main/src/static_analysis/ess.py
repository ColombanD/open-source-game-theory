"""Pure-strategy ESS enumeration on a row-player payoff matrix A.

ESS definition (Maynard-Smith two-condition form for a single-population
game with possibly asymmetric A; see Sandholm 2010 Ch. 8, Weibull 1995
Def. 2.1): type i is a pure ESS iff, for every j != i, at least one of

    (a)  A[i, i] >  A[j, i]                               (strict Nash)
    (b)  A[i, i] == A[j, i]  AND  A[i, j] > A[j, j]       (tiebreaker)

holds. The matrix A is NOT symmetrised.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Set, Tuple

import numpy as np  # type: ignore


@dataclass(frozen=True)
class PairRecord:
    """One ordered pair (i, j), i != j, with the ESS-clause evaluation."""

    i: str
    j: str
    A_ii: float
    A_ji: float
    A_ij: float
    A_jj: float
    clause_a_holds: bool
    tie_at_ji: bool
    clause_b_holds: bool
    i_survives_j: bool
    touches_suspect_cell: bool = False


@dataclass(frozen=True)
class TypeRecord:
    """Per-type aggregate verdict."""

    type: str
    is_ESS: bool
    n_invaders: int
    failing_invaders: Tuple[str, ...]
    notes: str = ""


@dataclass(frozen=True)
class EssResult:
    pairwise: Tuple[PairRecord, ...]
    summary: Tuple[TypeRecord, ...]


def enumerate_pure_ess(
    names: List[str],
    A: np.ndarray,
    atol: float = 1e-12,
) -> EssResult:
    """Enumerate pure-strategy ESS types of the single-population game on A."""
    n = len(names)
    if n == 0:
        raise ValueError("enumerate_pure_ess requires at least one type")
    if A.shape != (n, n):
        raise ValueError(f"A must be square of shape ({n}, {n}); got {A.shape}")
    if not np.all(np.isfinite(A)):
        raise ValueError(
            "A must contain only finite values; undefined cells must be resolved upstream"
        )

    pairwise: List[PairRecord] = []
    invaders: List[List[str]] = [[] for _ in range(n)]

    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            a_ii = float(A[i, i])
            a_ji = float(A[j, i])
            a_ij = float(A[i, j])
            a_jj = float(A[j, j])

            clause_a = a_ii > a_ji + atol
            tie_at_ji = abs(a_ii - a_ji) <= atol
            clause_b = tie_at_ji and (a_ij > a_jj + atol)
            i_survives_j = clause_a or clause_b

            pairwise.append(
                PairRecord(
                    i=names[i], j=names[j],
                    A_ii=a_ii, A_ji=a_ji, A_ij=a_ij, A_jj=a_jj,
                    clause_a_holds=clause_a,
                    tie_at_ji=tie_at_ji,
                    clause_b_holds=clause_b,
                    i_survives_j=i_survives_j,
                )
            )
            if not i_survives_j:
                invaders[i].append(names[j])

    pairwise.sort(key=lambda r: (r.i, r.j))

    summary = tuple(
        TypeRecord(
            type=names[i],
            is_ESS=(len(invaders[i]) == 0),
            n_invaders=len(invaders[i]),
            failing_invaders=tuple(sorted(invaders[i])),
        )
        for i in range(n)
    )

    return EssResult(pairwise=tuple(pairwise), summary=summary)


def flag_suspect_cells(
    result: EssResult,
    suspect_cells: Iterable[Tuple[str, str]],
) -> EssResult:
    """Stamp `touches_suspect_cell` on pairwise rows referencing any flagged
    cell, and set the corresponding `notes` on the affected type rows.

    A pairwise row (i, j) is flagged when any of (i, j), (j, i), (i, i),
    (j, j) appears in `suspect_cells`.
    """
    suspect_set: Set[Tuple[str, str]] = {(a, b) for (a, b) in suspect_cells}
    affected_types: Set[str] = set()

    new_pairwise = []
    for r in result.pairwise:
        cells = {(r.i, r.j), (r.j, r.i), (r.i, r.i), (r.j, r.j)}
        touches = bool(cells & suspect_set)
        if touches:
            affected_types.add(r.i)
        new_pairwise.append(
            PairRecord(
                i=r.i, j=r.j,
                A_ii=r.A_ii, A_ji=r.A_ji, A_ij=r.A_ij, A_jj=r.A_jj,
                clause_a_holds=r.clause_a_holds,
                tie_at_ji=r.tie_at_ji,
                clause_b_holds=r.clause_b_holds,
                i_survives_j=r.i_survives_j,
                touches_suspect_cell=touches,
            )
        )

    new_summary = tuple(
        TypeRecord(
            type=t.type,
            is_ESS=t.is_ESS,
            n_invaders=t.n_invaders,
            failing_invaders=t.failing_invaders,
            notes="depends on red cell" if t.type in affected_types else "",
        )
        for t in result.summary
    )

    return EssResult(pairwise=tuple(new_pairwise), summary=new_summary)

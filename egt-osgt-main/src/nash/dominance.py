"""Iterated pure strict dominance reducer for the bimatrix (A, A^T).

Strategy i is *purely* strictly dominated for the row player iff there
exists j ≠ i with A[j, k] > A[i, k] for all k. The reducer iteratively
removes such strategies (both players) until no more are removable.
This is sound but not complete: mixed-strategy dominators are not
considered, so some technically dominated strategies may survive. For
the OSGT game this is sufficient — the analyst can inspect the result.

The Nash-equilibrium set is invariant under iterated strict dominance,
so the survivors' NE set, embedded back into the full strategy space by
zero-padding, equals the full game's NE set.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple

import numpy as np  # type: ignore

from src.nash.game_construction import to_fraction_matrix


@dataclass(frozen=True)
class DominanceRemoval:
    player: str           # "row" or "col"
    strategy: int         # index in the *current* strategy set when removed
    strategy_name: str    # bot name for readability
    dominated_by: int     # index in the *current* strategy set
    dominated_by_name: str
    round: int


@dataclass(frozen=True)
class DominanceResult:
    survivors_row: List[int]      # indices into original A of strategies surviving for row
    survivors_col: List[int]      # indices for col player (will equal row in symmetric case)
    removals: List[DominanceRemoval]


def _strictly_dominated(M: List[List[Fraction]], i: int) -> int:
    """Return j != i that strictly dominates row i in matrix M, or -1 if none."""
    n = len(M)
    for j in range(n):
        if j == i:
            continue
        if all(M[j][k] > M[i][k] for k in range(n)):
            return j
    return -1


def reduce_iteratively(A: np.ndarray, names: List[str]) -> DominanceResult:
    """Apply iterated pure strict dominance until a fixed point."""
    n = A.shape[0]
    if n != len(names):
        raise ValueError(f"len(names) = {len(names)} != A.shape[0] = {n}")

    A_frac = to_fraction_matrix(A)
    surv_row: List[int] = list(range(n))
    surv_col: List[int] = list(range(n))
    removals: List[DominanceRemoval] = []

    round_idx = 0
    while True:
        round_idx += 1
        progress = False

        # Row player's matrix is A restricted to (surv_row, surv_col)
        Ar = [[A_frac[i][j] for j in surv_col] for i in surv_row]
        for local_i in range(len(Ar)):
            d = _strictly_dominated(Ar, local_i)
            if d != -1:
                global_i = surv_row[local_i]
                global_d = surv_row[d]
                removals.append(
                    DominanceRemoval(
                        player="row",
                        strategy=global_i,
                        strategy_name=names[global_i],
                        dominated_by=global_d,
                        dominated_by_name=names[global_d],
                        round=round_idx,
                    )
                )
                surv_row.pop(local_i)
                progress = True
                break

        # Col player's payoff vector at strategy j across surviving rows is
        # [B[i, j] for i in surv_row] = [A[j, i] for i in surv_row]
        # (because B = A^T). So col strategy j is strictly dominated by k
        # iff A[k, i] > A[j, i] for all surviving rows i.
        Bc = [[A_frac[j][i] for i in surv_row] for j in surv_col]
        for local_j in range(len(Bc)):
            d = _strictly_dominated(Bc, local_j)
            if d != -1:
                global_j = surv_col[local_j]
                global_d = surv_col[d]
                removals.append(
                    DominanceRemoval(
                        player="col",
                        strategy=global_j,
                        strategy_name=names[global_j],
                        dominated_by=global_d,
                        dominated_by_name=names[global_d],
                        round=round_idx,
                    )
                )
                surv_col.pop(local_j)
                progress = True
                break

        if not progress:
            break

    return DominanceResult(survivors_row=surv_row, survivors_col=surv_col, removals=removals)

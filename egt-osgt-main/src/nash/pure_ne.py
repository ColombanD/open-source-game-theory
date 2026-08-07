"""Direct enumeration of pure-strategy Nash equilibria of (A, A^T).

For (i, j) to be a pure NE of the bimatrix (A, A^T):
  - row's BR:  A[i, j] = max_k A[k, j]
  - col's BR:  A[j, i] = max_k A[k, i]   (since B = A^T, B[i, j] = A[j, i])

This O(N^3) check is a sanity net for the polytope-enumeration output:
every pure NE found here must appear in the Method 2 result.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List

from src.nash.game_construction import to_fraction_matrix
import numpy as np  # type: ignore


@dataclass(frozen=True)
class PureNE:
    i: int                # row strategy index
    j: int                # col strategy index
    u: Fraction           # row payoff at (i, j) in original A
    v: Fraction           # col payoff at (i, j) in original A


def enumerate_pure(A: np.ndarray) -> List[PureNE]:
    """Return all pure NE of the symmetric bimatrix (A, A^T)."""
    A_frac = to_fraction_matrix(A)
    n = len(A_frac)

    # Row's BR when col plays pure j: argmax over rows i of A[i, j].
    col_max = [max(A_frac[k][j] for k in range(n)) for j in range(n)]
    # Col's BR when row plays pure i: argmax over col strategies j of B[i, j]
    # = A[j, i]. So scan over the i-th column of A.
    col_max_for_i_played = col_max  # same vector, indexed by which column we read

    out: List[PureNE] = []
    for i in range(n):
        for j in range(n):
            row_br_ok = A_frac[i][j] == col_max[j]
            col_br_ok = A_frac[j][i] == col_max_for_i_played[i]
            if row_br_ok and col_br_ok:
                out.append(PureNE(i=i, j=j, u=A_frac[i][j], v=A_frac[j][i]))
    return out

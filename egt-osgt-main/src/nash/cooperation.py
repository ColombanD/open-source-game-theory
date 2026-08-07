"""Equilibrium cooperation rate Pr[(C, C)] under a mixed profile (xi, eta).

Pr[(C, C)] = sum_{i, j} xi[i] * eta[j] * 1{M[i][j] == ('C', 'C')}.

Numeric A loses the action-pair information (e.g. (C, C) and (D, D)
both round to integer payoffs), so the action-pair matrix M from
src.ingest is required.
"""

from __future__ import annotations

from fractions import Fraction
from typing import List, Tuple

from src.ingest.payoffs import ActionPair


def cooperation_rate(
    xi: List[Fraction],
    eta: List[Fraction],
    M: List[List[ActionPair]],
) -> Fraction:
    """Exact-rational probability that the pair plays (C, C)."""
    n = len(xi)
    if len(eta) != n or len(M) != n or any(len(row) != n for row in M):
        raise ValueError("xi, eta, M must all have matching dimensions")
    total = Fraction(0)
    for i in range(n):
        if xi[i] == 0:
            continue
        for j in range(n):
            if eta[j] == 0:
                continue
            if M[i][j] == ("C", "C"):
                total += xi[i] * eta[j]
    return total

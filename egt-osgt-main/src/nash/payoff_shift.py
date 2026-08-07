"""Payoff shift to make A entrywise positive.

Method 2's polytope construction P = {x ≥ 0, B^T x ≤ 1},
Q = {y ≥ 0, A y ≤ 1} requires A > 0 and B > 0 entrywise. We shift
A' = A + c_shift · J where c_shift = -min(A) + δ with δ = 1.

Adding the same constant to every entry leaves both players' best-
response correspondences unchanged, so the NE set of (A', B') equals
that of (A, B) exactly. Equilibrium payoffs differ by c_shift per
player and are recovered by subtraction.

c_shift is computed and used internally; it is never written back to
config.json.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple

DELTA: Fraction = Fraction(1)


@dataclass(frozen=True)
class ShiftRecord:
    c_shift: Fraction
    delta: Fraction
    min_before: Fraction
    min_after: Fraction


def shift_to_positive(
    A: List[List[Fraction]],
) -> Tuple[List[List[Fraction]], ShiftRecord]:
    """Return (A_shifted, record). Asserts (A_shifted > 0).all() exactly."""
    n = len(A)
    if n == 0 or any(len(row) != n for row in A):
        raise ValueError("A must be a non-empty square matrix")

    min_before = min(A[i][j] for i in range(n) for j in range(n))
    c_shift = -min_before + DELTA
    A_shift = [[A[i][j] + c_shift for j in range(n)] for i in range(n)]
    min_after = min(A_shift[i][j] for i in range(n) for j in range(n))

    if not all(A_shift[i][j] > 0 for i in range(n) for j in range(n)):
        raise AssertionError(
            f"shift to positive failed: min_after = {min_after}, c_shift = {c_shift}"
        )
    return A_shift, ShiftRecord(
        c_shift=c_shift, delta=DELTA, min_before=min_before, min_after=min_after
    )


def unshift_payoff(p_shifted: Fraction, c_shift: Fraction) -> Fraction:
    """Map a payoff in the shifted game back to the original game."""
    return p_shifted - c_shift

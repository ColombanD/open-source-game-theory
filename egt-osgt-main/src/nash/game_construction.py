"""Convert numpy float64 payoff matrix A to nested-list-of-Fraction.

Method 2 runs entirely in exact rational arithmetic. The OSGT default
configuration produces integer payoffs (b=3, c=1 ⇒ A ∈ {-1, 0, 2, 3});
the conversion is therefore lossless. For non-integer (b, c), values are
routed through `Fraction(str(x))` to avoid float-imprecision contamination.
"""

from __future__ import annotations

from fractions import Fraction
from typing import List, Tuple

import numpy as np  # type: ignore


def _to_fraction(x: float) -> Fraction:
    """Convert a float to Fraction safely.

    For values that are exact integers (e.g. -1.0, 0.0, 2.0, 3.0 from the
    OSGT default), use Fraction(int). Otherwise route via str(x) so the
    decimal representation is honoured rather than the binary float.
    """
    if float(x).is_integer():
        return Fraction(int(round(x)))
    return Fraction(str(x))


def to_fraction_matrix(A: np.ndarray) -> List[List[Fraction]]:
    """Numpy float matrix → nested list of Fraction. Asserts shape (N, N)."""
    if A.ndim != 2 or A.shape[0] != A.shape[1]:
        raise ValueError(f"A must be square, got shape {A.shape}")
    n = A.shape[0]
    return [[_to_fraction(A[i, j]) for j in range(n)] for i in range(n)]


def transpose(A: List[List[Fraction]]) -> List[List[Fraction]]:
    """Pure-Python transpose for a Fraction matrix."""
    n = len(A)
    return [[A[j][i] for j in range(n)] for i in range(n)]


def build_bimatrix(A: np.ndarray) -> Tuple[List[List[Fraction]], List[List[Fraction]]]:
    """Return the symmetric bimatrix (A, A^T) as Fraction matrices."""
    A_frac = to_fraction_matrix(A)
    B_frac = transpose(A_frac)
    return A_frac, B_frac

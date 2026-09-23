"""Subset enumeration over the type indices.

Yields every S ⊆ {0,…,N-1} with |S| ≥ 2 in lexicographic order of the
ordered tuple of indices. Order is fixed and deterministic so that
`support_id` is a stable column.
"""

from __future__ import annotations

from itertools import combinations
from typing import Iterator, Sequence, Tuple


def enumerate_supports(n: int) -> Iterator[Tuple[int, ...]]:
    """Yield supports as sorted index tuples, |S| from 2 to n inclusive."""
    if n < 2:
        return
    for k in range(2, n + 1):
        for combo in combinations(range(n), k):
            yield combo


def support_bitmask(support: Sequence[int], n: int) -> str:
    """Return a length-N bitmask string with '1' at positions in `support`."""
    bits = ["0"] * n
    for i in support:
        bits[i] = "1"
    return "".join(bits)


def support_tuple_str(support: Sequence[int], names: Sequence[str]) -> str:
    """Format a support as e.g. '(CooperateBot, DBot)' using readable names."""
    return "(" + ", ".join(names[i] for i in support) + ")"

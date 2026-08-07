"""Common dataclass for an extreme Nash equilibrium of (A, A^T).

Both Method-2 wrappers (pygambit, lrsnash) emit lists of `ExtremeNE`,
which `reconcile` then deduplicates and merges.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Optional, Tuple


@dataclass(frozen=True)
class ExtremeNE:
    xi: Tuple[Fraction, ...]
    eta: Tuple[Fraction, ...]
    support_x: Tuple[int, ...]      # indices where xi > 0
    support_y: Tuple[int, ...]      # indices where eta > 0
    finder: str                     # "pygambit" or "lrsnash"
    raw_index: int                  # 0-based index in the finder's emitted list
    label_set_size: Optional[int]   # only meaningful when the library reports it
    component_id: Optional[int]     # only when the library reports component IDs


def make_extreme_ne(
    xi: Tuple[Fraction, ...],
    eta: Tuple[Fraction, ...],
    finder: str,
    raw_index: int,
    label_set_size: Optional[int] = None,
    component_id: Optional[int] = None,
) -> ExtremeNE:
    """Build an ExtremeNE, computing supports from xi, eta."""
    support_x = tuple(i for i, p in enumerate(xi) if p > 0)
    support_y = tuple(j for j, p in enumerate(eta) if p > 0)
    return ExtremeNE(
        xi=xi,
        eta=eta,
        support_x=support_x,
        support_y=support_y,
        finder=finder,
        raw_index=raw_index,
        label_set_size=label_set_size,
        component_id=component_id,
    )

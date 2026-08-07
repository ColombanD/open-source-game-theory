"""Deduplicate extreme NE from multiple finders; cross-check libraries.

Two `ExtremeNE` records are equal iff their exact-rational (xi, eta)
tuples coincide. The reconciler:
  - merges by (xi, eta) key,
  - collects all `Discovery` records (one per (finder, raw_index, ...)),
  - asserts the deduplicated set from each finder is identical.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Dict, List, Optional, Tuple

from src.nash.extreme_ne import ExtremeNE


@dataclass(frozen=True)
class Discovery:
    finder: str
    raw_index: int
    label_set_size: Optional[int]
    component_id: Optional[int]


@dataclass
class ReconciledNE:
    xi: Tuple[Fraction, ...]
    eta: Tuple[Fraction, ...]
    support_x: Tuple[int, ...]
    support_y: Tuple[int, ...]
    discoveries: List[Discovery] = field(default_factory=list)


def _key(ne: ExtremeNE) -> Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]]:
    return (ne.xi, ne.eta)


def reconcile(
    pygambit_nes: List[ExtremeNE],
    lrsnash_nes: List[ExtremeNE],
) -> Tuple[List[ReconciledNE], bool, List[Tuple[Fraction, ...]]]:
    """Merge two lists; return (merged, libraries_agree, only_in_one_diagnostic).

    Libraries agree iff the deduplicated set from each finder is equal.
    The third return value is the symmetric-difference key list (empty
    on agreement) for the caller to print on failure.
    """
    table: Dict[Tuple[Tuple[Fraction, ...], Tuple[Fraction, ...]], ReconciledNE] = {}

    for ne_list in (pygambit_nes, lrsnash_nes):
        for ne in ne_list:
            k = _key(ne)
            if k not in table:
                table[k] = ReconciledNE(
                    xi=ne.xi,
                    eta=ne.eta,
                    support_x=ne.support_x,
                    support_y=ne.support_y,
                )
            table[k].discoveries.append(
                Discovery(
                    finder=ne.finder,
                    raw_index=ne.raw_index,
                    label_set_size=ne.label_set_size,
                    component_id=ne.component_id,
                )
            )

    pg_keys = {_key(ne) for ne in pygambit_nes}
    lr_keys = {_key(ne) for ne in lrsnash_nes}
    agree = pg_keys == lr_keys
    diff = sorted(pg_keys.symmetric_difference(lr_keys))

    # Preserve insertion order: pygambit-discovered NE first, then lrsnash-only.
    merged: List[ReconciledNE] = []
    seen: set = set()
    for ne in pygambit_nes:
        k = _key(ne)
        if k not in seen:
            merged.append(table[k])
            seen.add(k)
    for ne in lrsnash_nes:
        k = _key(ne)
        if k not in seen:
            merged.append(table[k])
            seen.add(k)

    return merged, agree, diff

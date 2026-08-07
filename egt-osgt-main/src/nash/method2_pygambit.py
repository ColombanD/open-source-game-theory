"""Method 2 enumeration via pygambit.nash.enummixed_solve(rational=True).

pygambit binds to lrslib internally and performs the same reverse-search
vertex enumeration on the best-response polytopes that the plan
prescribes. We pass it the *shifted* matrices so the upstream shift is
verifiably the one in effect, even though pygambit itself does not
require positive entries.
"""

from __future__ import annotations

from fractions import Fraction
from typing import List

import pygambit as gbt  # type: ignore

from src.nash.extreme_ne import ExtremeNE, make_extreme_ne


def _rational_to_fraction(r) -> Fraction:
    """Convert a pygambit.gambit.Rational to fractions.Fraction."""
    return Fraction(int(r.numerator), int(r.denominator))


def enumerate_pygambit(
    A_shifted: List[List[Fraction]],
    B_shifted: List[List[Fraction]],
) -> List[ExtremeNE]:
    """Return all extreme NE of (A_shifted, B_shifted) in exact rationals."""
    if not A_shifted or any(len(row) != len(B_shifted[0]) for row in A_shifted):
        raise ValueError("A_shifted and B_shifted must be conforming matrices")

    game = gbt.Game.from_arrays(A_shifted, B_shifted, title="osgt-method2")
    result = gbt.nash.enummixed_solve(game, rational=True)

    p_row = game.players[0]
    p_col = game.players[1]
    strategies_row = list(p_row.strategies)
    strategies_col = list(p_col.strategies)

    out: List[ExtremeNE] = []
    for idx, eq in enumerate(result.equilibria):
        xi = tuple(_rational_to_fraction(eq[s]) for s in strategies_row)
        eta = tuple(_rational_to_fraction(eq[s]) for s in strategies_col)
        out.append(
            make_extreme_ne(
                xi=xi,
                eta=eta,
                finder="pygambit",
                raw_index=idx,
                label_set_size=None,  # pygambit does not expose label-set size
                component_id=None,    # pygambit does not expose component IDs here
            )
        )
    return out

"""Prisoner's Dilemma payoffs and validation.

Payoff convention (row player's payoff as a function of (row_action, col_action)):

    (D, C) =  b
    (C, C) =  b - c
    (D, D) =  0
    (C, D) = -c

For this to define a Prisoner's Dilemma we require b > c > 0 (strict),
which yields the standard ordering T > R > P > S with T=b, R=b-c,
P=0, S=-c.
"""

from __future__ import annotations

from typing import Tuple

Action = str  # "C" or "D"
ActionPair = Tuple[Action, Action]


def validate_pd_params(b: float, c: float) -> None:
    """Raise ValueError unless b > c > 0 (strict)."""
    if not (isinstance(b, (int, float)) and isinstance(c, (int, float))):
        raise TypeError(f"b and c must be numeric, got b={type(b).__name__}, c={type(c).__name__}")
    if c <= 0:
        raise ValueError(f"c must be > 0 for a Prisoner's Dilemma, got c={c}")
    if b <= c:
        raise ValueError(f"b must be > c for a Prisoner's Dilemma, got b={b}, c={c}")


def row_payoff(pair: ActionPair, b: float, c: float) -> float:
    """Return the row player's payoff for action pair (row_action, col_action)."""
    a_row, a_col = pair
    if a_row == "D" and a_col == "C":
        return float(b)
    if a_row == "C" and a_col == "C":
        return float(b - c)
    if a_row == "D" and a_col == "D":
        return 0.0
    if a_row == "C" and a_col == "D":
        return float(-c)
    raise ValueError(f"Invalid action pair: {pair!r}; expected actions in {{'C', 'D'}}")


def parse_action_pair(s: str) -> ActionPair:
    """Parse a string like '(C, D)' or 'CD' into ('C', 'D')."""
    cleaned = s.strip().replace("(", "").replace(")", "").replace(" ", "").replace(",", "")
    if len(cleaned) != 2 or any(ch not in ("C", "D") for ch in cleaned):
        raise ValueError(f"Cannot parse action pair from {s!r}; expected two letters from {{C, D}}")
    return (cleaned[0], cleaned[1])

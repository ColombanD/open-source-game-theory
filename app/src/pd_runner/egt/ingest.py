"""Action-pair cells -> the real payoff matrix `A` the EGT stages consume.

This replaces the standalone repo's `src/ingest/` package, which parsed a
hand-transcribed CSV and imputed two special cells from a config file. Both of
those jobs are already done upstream and better:

  - the cells come from the theorem library via `tau.matrix`, so they are
    Lean-certified rather than transcribed;
  - open cells are resolved by RESTRICTING THE ZOO, so a `TauMatrix` is a
    TOTAL function on its bot list and nothing is imputed.

What survives from the old package is the PD payoff convention itself, which
is genuinely reusable and is reproduced here unchanged:

    (D, C) =  b        (C, C) =  b - c
    (D, D) =  0        (C, D) = -c

with `b > c > 0` (strict), giving the standard ordering T > R > P > S.

Three entry points, in increasing order of what they parameterize:

  - `payoff_matrix_from_cells`      — the primitive: cells -> A
  - `payoff_matrix_from_tau_matrix` — the base matrix (the t=1 anchor)
  - `payoff_matrix_from_tournament` — a tau tournament at fixed (t, α)

The last is what makes the `(t, α)` sweep possible: `TournamentResult.cells`
is already `dict[(row, col) -> (row_action, col_action)]`, exactly the shape
the old CSV parsed into.

## The "N" state

`tau.matrix` has a fifth cell state the EGT stages have no concept of: `"N"`,
a PROVEN `none` outcome (MirrorBot self-play — mutual simulation never
terminates). It is a kernel-backed value, not a missing entry.

There is no defensible payoff for "the match never returns", so this module
does not invent one. `NonTerminationPolicy` makes the choice explicit and
records it in the assumptions:

  - `"exclude"` (default) — drop every bot involved in an "N" cell before
    building `A`. This matches what the standalone repo did (it excluded
    MirrorBot outright) and is free on the default zoo, which has no "N".
  - `"payoff"` — assign a caller-supplied value to both sides. Only defensible
    if you can argue for the number; you must then report it.

Either way `assumptions()` carries the policy and the affected bots, so a
downstream reader can see that a choice was made.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Mapping, Sequence

import numpy as np

from pd_runner.tau.matrix import TauMatrix

Action = str  # "C" | "D" | "N"
ActionPair = tuple[str, str]

NonTerminationPolicy = Literal["exclude", "payoff"]

# The PD parameters. Defaults match the standalone repo's config.json, so a
# ported result is comparable to the ones checked in there.
DEFAULT_B = 3.0
DEFAULT_C = 1.0


class UndefinedPayoffError(ValueError):
    """Raised when a cell has no payoff under the configured policy."""


def validate_pd_params(b: float, c: float) -> None:
    """Raise ValueError unless b > c > 0 (strict)."""
    if not isinstance(b, (int, float)) or isinstance(b, bool):
        raise TypeError(f"b must be numeric, got {type(b).__name__}")
    if not isinstance(c, (int, float)) or isinstance(c, bool):
        raise TypeError(f"c must be numeric, got {type(c).__name__}")
    if c <= 0:
        raise ValueError(f"c must be > 0 for a Prisoner's Dilemma, got c={c}")
    if b <= c:
        raise ValueError(f"b must be > c for a Prisoner's Dilemma, got b={b}, c={c}")


def row_payoff(pair: ActionPair, b: float, c: float) -> float:
    """The ROW player's payoff for an action pair (row_action, col_action)."""
    a_row, a_col = pair
    if a_row == "D" and a_col == "C":
        return float(b)
    if a_row == "C" and a_col == "C":
        return float(b - c)
    if a_row == "D" and a_col == "D":
        return 0.0
    if a_row == "C" and a_col == "D":
        return float(-c)
    if "N" in (a_row, a_col):
        raise UndefinedPayoffError(
            f"non-terminating cell {pair!r} has no payoff; resolve it with a "
            "NonTerminationPolicy (see egt.ingest) rather than imputing one"
        )
    raise ValueError(f"Invalid action pair: {pair!r}; expected actions in {{C, D, N}}")


@dataclass(frozen=True)
class PayoffMatrix:
    """A real payoff matrix plus the provenance needed to interpret it.

    `A[i, j]` is the ROW player's payoff when type `i` meets type `j`. `A` is
    generally NOT symmetric — the EGT stages must use asymmetric-payoff forms
    of every formula.
    """

    bots: tuple[str, ...]
    A: np.ndarray
    cells: dict[ActionPair, ActionPair]
    b: float
    c: float
    # Bots dropped because they appeared in a non-terminating ("N") cell.
    excluded_bots: tuple[str, ...] = ()
    non_termination_policy: NonTerminationPolicy = "exclude"
    non_termination_payoff: float | None = None
    # Cells taken from a zoo's documented stipulations rather than from Lean.
    # Non-empty => every downstream result is CONDITIONAL on them.
    stipulated_cells: tuple[ActionPair, ...] = ()
    # Provenance of the action pairs: the base matrix, or a (t, α) tournament.
    source: str = "tau_matrix"
    t: float | None = None
    alpha: float | None = None
    zoo: str | None = None

    def __len__(self) -> int:
        return len(self.bots)

    @property
    def is_fully_proven(self) -> bool:
        """True when no cell rests on a stipulation."""
        return not self.stipulated_cells

    def assumptions(self) -> dict:
        """The provenance block every stage writes into `assumptions.json`."""
        return {
            "source": self.source,
            "zoo": self.zoo,
            "bots": list(self.bots),
            "n_types": len(self.bots),
            "pd_payoffs": {
                "parametrisation": "(b, c) with b > c > 0",
                "b": self.b,
                "c": self.c,
                # Nested under `implied_trps` because the stage report writers
                # read it there (inherited from the standalone repo's schema).
                "implied_trps": {
                    "T": self.b,
                    "R": self.b - self.c,
                    "P": 0.0,
                    "S": -self.c,
                },
                "convention": "row payoff: (D,C)=b, (C,C)=b-c, (D,D)=0, (C,D)=-c",
            },
            "tau": {"t": self.t, "alpha": self.alpha},
            "non_termination": {
                "policy": self.non_termination_policy,
                "payoff": self.non_termination_payoff,
                "excluded_bots": list(self.excluded_bots),
            },
            "stipulated_cells": [list(p) for p in self.stipulated_cells],
            "is_fully_proven": self.is_fully_proven,
        }


def _bots_in_non_terminating_cells(
    bots: Sequence[str],
    cells: Mapping[ActionPair, ActionPair],
) -> tuple[str, ...]:
    """Every bot appearing on either side of an "N" cell, in `bots` order."""
    hit: set[str] = set()
    for (row, col), pair in cells.items():
        if "N" in pair:
            hit.add(row)
            hit.add(col)
    return tuple(b for b in bots if b in hit)


def payoff_matrix_from_cells(
    bots: Sequence[str],
    cells: Mapping[ActionPair, ActionPair],
    *,
    b: float = DEFAULT_B,
    c: float = DEFAULT_C,
    non_termination: NonTerminationPolicy = "exclude",
    non_termination_payoff: float | None = None,
    stipulated_cells: Sequence[ActionPair] = (),
    source: str = "cells",
    t: float | None = None,
    alpha: float | None = None,
    zoo: str | None = None,
) -> PayoffMatrix:
    """Action-pair cells -> `PayoffMatrix`. The primitive both loaders call.

    `cells` must be TOTAL over `bots × bots` (after any "N" exclusion): a
    missing cell raises rather than defaulting, because silently imputing an
    outcome is exactly the failure mode the zoo-restriction convention exists
    to prevent.
    """
    validate_pd_params(b, c)

    if non_termination == "payoff" and non_termination_payoff is None:
        raise ValueError(
            "non_termination='payoff' requires an explicit non_termination_payoff"
        )

    bots = tuple(bots)
    excluded: tuple[str, ...] = ()
    if non_termination == "exclude":
        excluded = _bots_in_non_terminating_cells(bots, cells)
        if excluded:
            keep = set(bots) - set(excluded)
            bots = tuple(x for x in bots if x in keep)

    n = len(bots)
    if n == 0:
        raise ValueError(
            "no bots left to analyse"
            + (f" after excluding {list(excluded)} for non-termination" if excluded else "")
        )

    A = np.zeros((n, n), dtype=float)
    kept_cells: dict[ActionPair, ActionPair] = {}
    for i, row in enumerate(bots):
        for j, col in enumerate(bots):
            try:
                pair = cells[(row, col)]
            except KeyError:
                raise UndefinedPayoffError(
                    f"missing cell for ({row}, {col}); the payoff matrix must be "
                    "total over the zoo — restrict the zoo rather than impute"
                ) from None
            kept_cells[(row, col)] = tuple(pair)  # type: ignore[assignment]
            if "N" in pair:
                # Only reachable under the "payoff" policy; "exclude" dropped it.
                A[i, j] = float(non_termination_payoff)  # type: ignore[arg-type]
            else:
                A[i, j] = row_payoff(tuple(pair), b, c)  # type: ignore[arg-type]

    kept = set(bots)
    return PayoffMatrix(
        bots=bots,
        A=A,
        cells=kept_cells,
        b=b,
        c=c,
        excluded_bots=excluded,
        non_termination_policy=non_termination,
        non_termination_payoff=non_termination_payoff,
        stipulated_cells=tuple(
            p for p in stipulated_cells if p[0] in kept and p[1] in kept
        ),
        source=source,
        t=t,
        alpha=alpha,
        zoo=zoo,
    )


def payoff_matrix_from_tau_matrix(
    matrix: TauMatrix,
    *,
    b: float = DEFAULT_B,
    c: float = DEFAULT_C,
    non_termination: NonTerminationPolicy = "exclude",
    non_termination_payoff: float | None = None,
    zoo: str | None = None,
) -> PayoffMatrix:
    """The BASE outcome matrix -> `A`.

    This is the `t = 1` anchor: at full transparency the tau tournament
    reproduces the base matrix exactly (the anchor theorem), so running the
    EGT stages on this is the same as running them at `t = 1`.
    """
    cells = {
        (row, col): (
            matrix.cell(row, col).row_action,
            matrix.cell(row, col).col_action,
        )
        for row in matrix.bots
        for col in matrix.bots
    }
    return payoff_matrix_from_cells(
        matrix.bots,
        cells,
        b=b,
        c=c,
        non_termination=non_termination,
        non_termination_payoff=non_termination_payoff,
        stipulated_cells=matrix.hypothetical_cells,
        source="tau_matrix_base",
        t=1.0,
        alpha=None,
        zoo=zoo,
    )


def payoff_matrix_from_tournament(
    result,
    *,
    bots: Sequence[str] | None = None,
    b: float = DEFAULT_B,
    c: float = DEFAULT_C,
    non_termination: NonTerminationPolicy = "exclude",
    non_termination_payoff: float | None = None,
    stipulated_cells: Sequence[ActionPair] = (),
    zoo: str | None = None,
) -> PayoffMatrix:
    """A tau tournament at fixed `(t, α)` -> `A`. The `(t, α)` entry point.

    `result` is a `tau.sweep.TournamentResult`, whose `cells` map is already
    `(row, col) -> (row_action, col_action)`. `bots` fixes the row/column
    ORDER; when omitted it is recovered from the cell keys in first-seen
    order, which for a tournament built by `run_tournament` is `matrix.bots`.
    """
    if bots is None:
        seen: list[str] = []
        for row, _ in result.cells:
            if row not in seen:
                seen.append(row)
        bots = tuple(seen)

    return payoff_matrix_from_cells(
        bots,
        result.cells,
        b=b,
        c=c,
        non_termination=non_termination,
        non_termination_payoff=non_termination_payoff,
        stipulated_cells=stipulated_cells,
        source=f"tau_tournament[{result.family}]",
        t=result.t,
        alpha=result.alpha,
        zoo=zoo,
    )

"""Load the numeric payoff matrix A and the action-pair matrix M.

Numeric A comes from `invasion.loader.load_numeric_A` so the Nash stage
shares its inputs exactly with the invasion and faces stages. The
action-pair matrix M comes along with it on the `PayoffMatrix`, because A
alone cannot recover Pr[(C, C)] at an equilibrium — the map from payoff
value back to action pair is one-to-many ((C,C) and (D,D) are distinct
outcomes, and under some conventions equal payoffs).
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional

import numpy as np  # type: ignore

from pd_runner.egt.ingest import ActionPair, PayoffMatrix
from pd_runner.egt.invasion.loader import LoadResult, load_numeric_A


@dataclass(frozen=True)
class LoadBundle:
    bot_names: List[str]
    A: np.ndarray                     # float64; shape (N, N)
    M: List[List[ActionPair]]         # action-pair matrix; M[i][j] = ('C'|'D','C'|'D')
    assumptions: dict                 # the PayoffMatrix provenance block
    numeric_csv: Path
    inherited_assumptions: Optional[dict]
    cross_checked: bool
    cross_check_max_abs_diff: Optional[float]


def load_bundle(
    payoff: PayoffMatrix,
    numeric_csv: Path,
    inherited_assumptions_path: Optional[Path] = None,
    atol: float = 1e-12,
) -> LoadBundle:
    """Return everything the Nash stage needs in one call.

    `payoff` is the run's `egt.ingest.PayoffMatrix`; it supplies both the
    action-pair matrix M and the cross-check copy of A.
    """
    lr: LoadResult = load_numeric_A(
        numeric_csv=numeric_csv,
        rebuilt=payoff,
        inherited_assumptions_path=inherited_assumptions_path,
        atol=atol,
    )

    M: List[List[ActionPair]] = [
        [payoff.cells[(row, col)] for col in payoff.bots] for row in payoff.bots
    ]

    return LoadBundle(
        bot_names=lr.bot_names,
        A=lr.A,
        M=M,
        assumptions=payoff.assumptions(),
        numeric_csv=Path(numeric_csv),
        inherited_assumptions=lr.inherited_assumptions,
        cross_checked=lr.cross_checked,
        cross_check_max_abs_diff=lr.cross_check_max_abs_diff,
    )


def hash_payoff_matrix(payoff: PayoffMatrix) -> str:
    """SHA-256 over the action-pair cells — the run's input fingerprint.

    Replaces the standalone repo's hash of the source CSV file: there is no
    input file any more, so the identity of a run is the cells themselves
    (plus the bot order, which is part of the matrix's meaning).
    """
    import hashlib

    h = hashlib.sha256()
    for row in payoff.bots:
        for col in payoff.bots:
            pair = payoff.cells[(row, col)]
            h.update(f"{row}|{col}|{pair[0]}{pair[1]}\n".encode())
    return h.hexdigest()

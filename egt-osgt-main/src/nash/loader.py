"""Load the numeric payoff matrix A and the action-pair matrix M.

Numeric A comes from `src.invasion.loader.load_numeric_A` so the Nash
stage shares its inputs exactly with the invasion and faces stages.
The action-pair matrix M is reconstructed via `src.ingest.matrix_loader`
because A alone cannot recover Pr[(C, C)] at an equilibrium (the inverse
map from payoff value to action pair is one-to-many).
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple

import numpy as np  # type: ignore

from src.ingest.matrix_loader import load_action_pair_matrix, resolve_undefined
from src.ingest.payoffs import ActionPair
from src.invasion.loader import LoadResult, load_numeric_A


@dataclass(frozen=True)
class LoadBundle:
    bot_names: List[str]
    A: np.ndarray                     # float64; shape (N, N)
    M: List[List[ActionPair]]         # action-pair matrix; M[i][j] = ('C'|'D','C'|'D')
    config: dict                      # parsed config.json
    raw_csv: Path
    config_path: Path
    numeric_csv: Path
    inherited_assumptions: Optional[dict]
    cross_checked: bool
    cross_check_max_abs_diff: Optional[float]


def load_bundle(
    raw_csv: Path,
    config_path: Path,
    numeric_csv: Path,
    inherited_assumptions_path: Optional[Path],
    atol: float = 1e-12,
) -> LoadBundle:
    """Return everything the Nash stage needs in one call."""
    with open(config_path) as f:
        config = json.load(f)

    lr: LoadResult = load_numeric_A(
        numeric_csv=numeric_csv,
        raw_csv=raw_csv,
        config=config_path,
        inherited_assumptions_path=inherited_assumptions_path,
        atol=atol,
    )

    pair_names, pair_matrix_raw = load_action_pair_matrix(raw_csv)
    if pair_names != lr.bot_names:
        raise ValueError(
            f"bot name disagreement between numeric CSV ({lr.bot_names}) "
            f"and raw CSV ({pair_names})"
        )
    M = resolve_undefined(pair_names, pair_matrix_raw, config)

    return LoadBundle(
        bot_names=lr.bot_names,
        A=lr.A,
        M=M,
        config=config,
        raw_csv=Path(raw_csv),
        config_path=Path(config_path),
        numeric_csv=Path(numeric_csv),
        inherited_assumptions=lr.inherited_assumptions,
        cross_checked=lr.cross_checked,
        cross_check_max_abs_diff=lr.cross_check_max_abs_diff,
    )


def hash_input_csv(raw_csv: Path) -> str:
    """SHA-256 of the raw action-pair CSV file contents."""
    import hashlib

    h = hashlib.sha256()
    with open(raw_csv, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()

"""Load the action-pair CSV and convert it to a real payoff matrix A.

`A[i, j]` is the row player's payoff when row-type i is paired with
column-type j, under the PD payoff convention defined in
`src.ingest.payoffs`. The matrix is generally NOT symmetric.
"""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import List, Mapping, Tuple

import numpy as np # type: ignore

from .payoffs import ActionPair, parse_action_pair, row_payoff, validate_pd_params
from .undefined_policy import UNDEFINED, resolve_cupod_vs_dupoc


def load_action_pair_matrix(
    csv_path: Path,
) -> Tuple[List[str], List[List[ActionPair | None]]]:
    """Read the CSV and return (bot_names, matrix-of-action-pairs-or-None)."""
    with open(csv_path, newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        bot_names = header[1:]
        rows = []
        for raw in reader:
            if not raw:
                continue
            label, *cells = raw
            if label != bot_names[len(rows)]:
                raise ValueError(
                    f"Row label {label!r} does not match column header "
                    f"{bot_names[len(rows)]!r} at index {len(rows)}"
                )
            parsed = [parse_action_pair(c) if c.strip() else UNDEFINED for c in cells]
            rows.append(parsed)
    if len(rows) != len(bot_names):
        raise ValueError(
            f"CSV has {len(bot_names)} columns but {len(rows)} rows; expected square matrix"
        )
    return bot_names, rows


def resolve_undefined(
    bot_names: List[str],
    pair_matrix: List[List[ActionPair | None]],
    config: Mapping,
) -> List[List[ActionPair]]:
    """Replace every UNDEFINED entry with a configured action pair.

    Currently only `(CupodBot, DupocBot)` (and its transpose) is undefined.
    """
    n = len(bot_names)
    name_to_idx = {name: i for i, name in enumerate(bot_names)}
    resolved: List[List[ActionPair]] = [list(row) for row in pair_matrix]  # type: ignore[arg-type]

    if "CupodBot" in name_to_idx and "DupocBot" in name_to_idx:
        i = name_to_idx["CupodBot"]
        j = name_to_idx["DupocBot"]
        cupod_dupoc = resolve_cupod_vs_dupoc(config)
        if resolved[i][j] is UNDEFINED:
            resolved[i][j] = cupod_dupoc
        if resolved[j][i] is UNDEFINED:
            resolved[j][i] = (cupod_dupoc[1], cupod_dupoc[0])  # transpose by game-symmetry

    for i in range(n):
        for j in range(n):
            if resolved[i][j] is UNDEFINED:
                raise ValueError(
                    f"Unresolved undefined cell at ({bot_names[i]}, {bot_names[j]}); "
                    "extend resolve_undefined() or update config."
                )
    return resolved  # type: ignore[return-value]


def build_payoff_matrix(
    pair_matrix: List[List[ActionPair]], b: float, c: float
) -> np.ndarray:
    """Convert an action-pair matrix to the row player's real payoff matrix."""
    validate_pd_params(b, c)
    n = len(pair_matrix)
    A = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            A[i, j] = row_payoff(pair_matrix[i][j], b, c)
    return A


def load_payoff_matrix(
    csv_path: Path, config_path: Path
) -> Tuple[List[str], np.ndarray]:
    """End-to-end: CSV + config → (bot_names, real payoff matrix A)."""
    with open(config_path) as f:
        config = json.load(f)
    pd_params = config["prisoners_dilemma"]
    b, c = pd_params["b"], pd_params["c"]

    bot_names, pair_matrix = load_action_pair_matrix(csv_path)
    resolved = resolve_undefined(bot_names, pair_matrix, config)
    A = build_payoff_matrix(resolved, b, c)
    return bot_names, A

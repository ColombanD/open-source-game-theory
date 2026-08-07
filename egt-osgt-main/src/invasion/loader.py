"""Load the numeric payoff matrix A for invasion-graph analysis.

Primary source: `results/ess/payoff_matrix_numeric.csv`, written by the
ESS pipeline. We reuse it so PD conventions stay locked across analyses.

Defence in depth: if `data/payoff_matrix.csv` and `config.json` are
available, rebuild A from them via `src.ingest.matrix_loader` and assert
exact equality (within `atol`). On disagreement the caller is told.
"""

from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple

import numpy as np  # type: ignore


@dataclass(frozen=True)
class LoadResult:
    bot_names: List[str]
    A: np.ndarray
    source: str                       # "results/ess/..." or "rebuilt from data/"
    cross_checked: bool               # True if rebuilt copy matched
    cross_check_max_abs_diff: Optional[float]
    inherited_assumptions: Optional[dict]   # parsed results/ess/assumptions.json


def _read_numeric_csv(path: Path) -> Tuple[List[str], np.ndarray]:
    with open(path, newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        names = [h for h in header[1:] if h != ""]
        rows: List[List[float]] = []
        labels: List[str] = []
        for raw in reader:
            if not raw or all(c == "" for c in raw):
                continue
            label, *cells = raw
            labels.append(label)
            rows.append([float(c) for c in cells[: len(names)]])
    if labels != names:
        raise ValueError(
            f"Row labels {labels} do not match column header {names} in {path}"
        )
    return names, np.array(rows, dtype=float)


def load_numeric_A(
    numeric_csv: Path,
    raw_csv: Optional[Path] = None,
    config: Optional[Path] = None,
    inherited_assumptions_path: Optional[Path] = None,
    atol: float = 1e-12,
) -> LoadResult:
    """Load A from `numeric_csv`; if `raw_csv` and `config` are given, rebuild
    A from them and cross-check.

    Returns a `LoadResult` carrying the chosen A, the source string, and the
    cross-check outcome. Raises ValueError if the two copies disagree by
    more than `atol`.
    """
    numeric_csv = Path(numeric_csv)
    names, A = _read_numeric_csv(numeric_csv)
    source = str(numeric_csv)

    inherited: Optional[dict] = None
    if inherited_assumptions_path is not None:
        p = Path(inherited_assumptions_path)
        if p.exists():
            with open(p) as f:
                inherited = json.load(f)

    cross_checked = False
    max_abs_diff: Optional[float] = None
    if raw_csv is not None and config is not None:
        raw_csv = Path(raw_csv)
        config = Path(config)
        if raw_csv.exists() and config.exists():
            from src.ingest.matrix_loader import load_payoff_matrix

            names_rebuilt, A_rebuilt = load_payoff_matrix(raw_csv, config)
            if names_rebuilt != names:
                raise ValueError(
                    f"bot name disagreement between {numeric_csv} ({names}) "
                    f"and rebuild from {raw_csv} ({names_rebuilt})"
                )
            diff = float(np.max(np.abs(A - A_rebuilt)))
            max_abs_diff = diff
            if diff > atol:
                raise ValueError(
                    f"numeric matrix at {numeric_csv} disagrees with rebuild "
                    f"from {raw_csv} (max |Δ| = {diff:g} > atol = {atol:g}); "
                    "refusing to silently override."
                )
            cross_checked = True

    return LoadResult(
        bot_names=names,
        A=A,
        source=source,
        cross_checked=cross_checked,
        cross_check_max_abs_diff=max_abs_diff,
        inherited_assumptions=inherited,
    )

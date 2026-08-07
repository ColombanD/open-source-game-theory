"""Load the numeric payoff matrix A for invasion-graph analysis.

Primary source: the `payoff_matrix_numeric.csv` written by the ESS stage into
the current run directory. We reuse it so PD conventions stay locked across
the four stages — that CSV is the inter-stage contract.

Defence in depth: the caller may also pass the in-memory `PayoffMatrix` the
ESS stage built (see `egt.ingest`), in which case A is rebuilt-checked for
exact equality (within `atol`), bot ORDER included. On disagreement the
caller is told rather than silently overridden.
"""

from __future__ import annotations

import csv
import json
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING, List, Optional, Tuple

import numpy as np  # type: ignore

if TYPE_CHECKING:
    from pd_runner.egt.ingest import PayoffMatrix


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
    rebuilt: Optional["PayoffMatrix"] = None,
    inherited_assumptions_path: Optional[Path] = None,
    atol: float = 1e-12,
) -> LoadResult:
    """Load A from `numeric_csv`, optionally cross-checked against `rebuilt`.

    `rebuilt` is an in-memory `egt.ingest.PayoffMatrix` for the SAME run — the
    stage that wrote `numeric_csv` still holds it. Passing it re-runs the
    defence-in-depth check the standalone repo did against its source CSV:
    the two copies must agree on bot ORDER and on every entry. That is what
    catches a zoo-ordering bug, which is the realistic failure mode here now
    that A is built from a bot list rather than parsed from a fixed file.

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
    if rebuilt is not None:
        names_rebuilt = list(rebuilt.bots)
        if names_rebuilt != names:
            raise ValueError(
                f"bot name disagreement between {numeric_csv} ({names}) "
                f"and the in-memory rebuild ({names_rebuilt})"
            )
        diff = float(np.max(np.abs(A - rebuilt.A)))
        max_abs_diff = diff
        if diff > atol:
            raise ValueError(
                f"numeric matrix at {numeric_csv} disagrees with the in-memory "
                f"rebuild (max |Δ| = {diff:g} > atol = {atol:g}); "
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

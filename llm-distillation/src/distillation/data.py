"""Data loading and parsing for the payoff matrix.

The payoff matrix is a square CSV of a two-player, two-action game with actions
in {C, D}. Cell (row A, column B) encodes a pair ``(row_action, col_action)``:
the action the *row* bot plays against the column bot, and the action the column
bot plays against the row bot.

For bot ``i`` the **reference vector** ``r_i`` is row ``i``'s OWN action across
every opponent column ``j`` -- i.e. the FIRST element of the pair in cell
``(i, j)``. This is "what bot ``i`` does against each opponent". We never use the
second (column-action) half, and we never transpose.

Action -> probability convention, used consistently everywhere in the codebase:

    C -> 1   (cooperate)
    D -> 0   (defect)

The canonical bot ordering is the CSV's row order; it is reused for every vector,
matrix, and output.
"""

from __future__ import annotations

import csv
import re
from dataclasses import dataclass
from pathlib import Path

import numpy as np

# Maps a single action character to its probability under the C=1, D=0 convention.
ACTION_TO_PROB = {"C": 1.0, "D": 0.0}

# Matches a cell of the form "(C, D)", "(C,D)", "C,D", "CD", with optional spaces.
_CELL_RE = re.compile(r"^\(?\s*([CD])\s*,?\s*([CD])\s*\)?$")


@dataclass(frozen=True)
class ReferenceLibrary:
    """A parsed payoff matrix expressed as reference vectors.

    Attributes:
        bots: Canonical bot ordering (CSV row order).
        R: ``N x N`` matrix of reference vectors. ``R[i, j]`` is bot ``i``'s own
            action against opponent ``j``, as a probability (C=1, D=0). Row ``i``
            is the reference vector ``r_i``.
    """

    bots: tuple[str, ...]
    R: np.ndarray

    @property
    def n(self) -> int:
        return len(self.bots)


def parse_cell(cell: str) -> tuple[float, float]:
    """Parse one matrix cell into ``(row_prob, col_prob)`` under C=1, D=0.

    Accepts the common encodings: ``"(C, D)"``, ``"(C,D)"``, ``"C,D"``, ``"CD"``.
    """
    match = _CELL_RE.match(cell.strip())
    if match is None:
        raise ValueError(f"Cannot parse cell {cell!r}: expected a pair of C/D actions")
    row_action, col_action = match.group(1), match.group(2)
    return ACTION_TO_PROB[row_action], ACTION_TO_PROB[col_action]


def load_library(path: str | Path) -> ReferenceLibrary:
    """Load and parse the payoff matrix CSV into a :class:`ReferenceLibrary`.

    The CSV is expected to have a header row of opponent names (with an empty
    top-left corner cell) and one row per bot, each cell encoding the action
    pair. The matrix must be square and fully populated, and the row order must
    match the column order (same canonical bot set).
    """
    path = Path(path)
    with path.open(newline="") as f:
        rows = [row for row in csv.reader(f) if any(field.strip() for field in row)]

    if not rows:
        raise ValueError(f"{path} is empty")

    header = rows[0]
    column_bots = [name.strip() for name in header[1:]]
    row_bots: list[str] = []
    reference_rows: list[list[float]] = []

    for record in rows[1:]:
        row_bots.append(record[0].strip())
        # Keep only the row bot's own action (first element of each pair).
        reference_rows.append([parse_cell(cell)[0] for cell in record[1:]])

    R = np.asarray(reference_rows, dtype=float)

    _validate(row_bots, column_bots, R)
    return ReferenceLibrary(bots=tuple(row_bots), R=R)


def _validate(row_bots: list[str], column_bots: list[str], R: np.ndarray) -> None:
    n = len(row_bots)
    if R.shape != (n, n):
        raise ValueError(f"Matrix is not square: parsed shape {R.shape} for {n} bots")
    if row_bots != column_bots:
        raise ValueError(
            "Row order does not match column order; the bot set / ordering is "
            f"inconsistent.\n  rows:    {row_bots}\n  columns: {column_bots}"
        )
    if len(set(row_bots)) != n:
        raise ValueError(f"Duplicate bot names in the matrix: {row_bots}")


def parse_cd_string(text: str) -> np.ndarray:
    """Parse a bare C/D string (e.g. ``"CDCC"``) into a {1, 0} probability vector.

    Separators (commas, spaces) are ignored, so ``"C,D,C"`` works too.
    """
    chars = [c for c in text.upper() if c in "CD"]
    if not chars:
        raise ValueError(f"No C/D actions found in {text!r}")
    return np.array([ACTION_TO_PROB[c] for c in chars], dtype=float)


def load_input_vector(arg: str | Path, n: int) -> np.ndarray:
    """Load the input profile ``x`` from a file or an inline C/D string.

    Resolution order:

    1. If ``arg`` is an existing file, parse it as JSON (a list of floats) or as
       CSV/whitespace-separated floats, or -- if it holds only C/D characters --
       as a C/D string.
    2. Otherwise treat ``arg`` itself as either a C/D string or a comma/space
       separated list of floats.

    The result is validated to have length ``n`` and to lie within ``[0, 1]``.
    """
    text = _read_arg(arg)
    x = _parse_vector_text(text)
    if x.shape != (n,):
        raise ValueError(f"Input vector has length {x.shape[0]}, expected {n}")
    if np.any(x < -1e-9) or np.any(x > 1 + 1e-9):
        raise ValueError(f"Input vector has entries outside [0, 1]: {x}")
    return np.clip(x, 0.0, 1.0)


def _read_arg(arg: str | Path) -> str:
    path = Path(arg)
    try:
        if path.is_file():
            return path.read_text()
    except OSError:
        pass
    return str(arg)


def _parse_vector_text(text: str) -> np.ndarray:
    import json

    stripped = text.strip()
    # JSON list of floats.
    if stripped.startswith("["):
        return np.asarray(json.loads(stripped), dtype=float)
    # Bare C/D string (only C/D and separators present).
    letters = set(stripped.upper()) - set(" ,\n\t\r")
    if letters and letters <= {"C", "D"}:
        return parse_cd_string(stripped)
    # Otherwise: comma / whitespace separated floats.
    tokens = [tok for tok in re.split(r"[,\s]+", stripped) if tok]
    return np.asarray([float(tok) for tok in tokens], dtype=float)


def format_reference_matrix(library: ReferenceLibrary) -> str:
    """Render the parsed ``N x N`` reference matrix R for eyeballing vs. source.

    Rows = bots, columns = opponents, entries in {0, 1}.
    """
    bots = library.bots
    width = max((len(b) for b in bots), default=4)
    # Short column headers (first 6 chars) keep the grid readable.
    col_labels = [b[:6] for b in bots]
    col_w = max(len(c) for c in col_labels)

    header = " " * width + " | " + " ".join(c.rjust(col_w) for c in col_labels)
    lines = [header, "-" * len(header)]
    for i, bot in enumerate(bots):
        entries = " ".join(
            str(int(round(v))).rjust(col_w) for v in library.R[i]
        )
        lines.append(f"{bot.ljust(width)} | {entries}")
    return "\n".join(lines)

"""Outcome matrix from the proven theorem library.

Scans `engine/PrisonersDilemma/Theorems/**/*.lean` for the unified
`outcome_Bot1_vs_Bot2` theorems and renders an upper-triangular matrix of
proven outcomes. Purely static — no LLM, no Lean invocation; the Lean kernel
already checked every cell.

Run with:
    uv run python -m pd_runner.eval.outcome_matrix
    uv run python -m pd_runner.eval.outcome_matrix --format md
    uv run python -m pd_runner.eval.outcome_matrix --format csv --output matrix.csv
    uv run python -m pd_runner.eval.outcome_matrix --annotate --output matrix.tsv
"""

from __future__ import annotations

import argparse
import csv
import io
import re
from dataclasses import dataclass
from pathlib import Path


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_THEOREMS_DIR = _workspace_root() / "engine" / "PrisonersDilemma" / "Theorems"

# Row/column order for the rendered matrix; discovered bots not listed here
# are appended alphabetically.
_CANONICAL_ORDER = [
    "CooperateBot",
    "CupodBot",
    "DBot",
    "DefectBot",
    "DupocBot",
    "OBot",
    "TitForTatBot",
    "MirrorBot",
    "EBot",
    "CupodTrollBot",
    "PrudentBot",
    "JustBot",
    "CIMCIC",
    "DIMCID",
]

_THEOREM_RE = re.compile(
    r"theorem\s+(outcome_(\w+?)_vs_(\w+?))\s*[({\[:].*?:=",
    re.DOTALL,
)
_PAIR_RE = re.compile(r"=\s*some\s*\(\s*\.([CD])\s*,\s*\.([CD])\s*\)")
_NONE_RE = re.compile(r"=\s*none\b")


@dataclass(frozen=True)
class OutcomeTheorem:
    name: str
    left_bot: str
    right_bot: str
    # ("C", "D") for a proven action pair, None for a proven no-outcome.
    pair: tuple[str, str] | None
    # "universal" | "existential" (∃k) | "threshold" (∃k₂, ∀k>k₂) | "no_outcome"
    shape: str
    file: str


def scan_outcome_theorems(theorems_dir: Path = _THEOREMS_DIR) -> list[OutcomeTheorem]:
    """Collect every `outcome_X_vs_Y` theorem with its proven result."""
    theorems: list[OutcomeTheorem] = []
    for lean_file in sorted(theorems_dir.rglob("*.lean")):
        content = lean_file.read_text(encoding="utf-8")
        for match in _THEOREM_RE.finditer(content):
            name, left, right = match.group(1), match.group(2), match.group(3)
            statement = match.group(0)

            pair_match = _PAIR_RE.search(statement)
            if pair_match:
                pair: tuple[str, str] | None = (pair_match.group(1), pair_match.group(2))
                if "∀" in statement:
                    shape = "threshold"
                elif "∃" in statement:
                    shape = "existential"
                else:
                    shape = "universal"
            elif _NONE_RE.search(statement):
                pair, shape = None, "no_outcome"
            else:
                continue  # not an outcome statement (e.g. helper with a lookalike name)

            theorems.append(OutcomeTheorem(name, left, right, pair, shape, lean_file.name))
    return theorems


def _bot_order(theorems: list[OutcomeTheorem]) -> list[str]:
    discovered = {t.left_bot for t in theorems} | {t.right_bot for t in theorems}
    ordered = [b for b in _CANONICAL_ORDER if b in discovered]
    ordered += sorted(discovered - set(ordered))
    return ordered


def build_outcome_matrix(
    theorems_dir: Path = _THEOREMS_DIR,
    missing: str = "Open Problem",
    annotate: bool = False,
) -> tuple[list[str], dict[tuple[str, str], str]]:
    """Upper-triangular matrix of proven outcomes.

    Returns (bot order, cells) where cells maps (row_bot, col_bot) with
    row index ≤ column index to a rendered value. A cell reads from the row
    bot's perspective: (row's action, column's action). When only the
    reversed theorem exists, its pair is swapped to fit.
    """
    theorems = scan_outcome_theorems(theorems_dir)
    by_pair = {(t.left_bot, t.right_bot): t for t in theorems}
    bots = _bot_order(theorems)

    def render(t: OutcomeTheorem, swapped: bool) -> str:
        if t.pair is None:
            return "none"
        a, b = (t.pair[1], t.pair[0]) if swapped else t.pair
        cell = f"({a}, {b})"
        if annotate and t.shape == "existential":
            cell += " ∃k"
        elif annotate and t.shape == "threshold":
            cell += " k≫"
        return cell

    cells: dict[tuple[str, str], str] = {}
    for i, row in enumerate(bots):
        for col in bots[i:]:
            if (row, col) in by_pair:
                cells[(row, col)] = render(by_pair[(row, col)], swapped=False)
            elif (col, row) in by_pair:
                cells[(row, col)] = render(by_pair[(col, row)], swapped=True)
            else:
                cells[(row, col)] = missing
    return bots, cells


def format_matrix(
    bots: list[str],
    cells: dict[tuple[str, str], str],
    fmt: str = "tsv",
) -> str:
    header = ["Outcome Matrix", *bots]
    rows = [header]
    for i, row_bot in enumerate(bots):
        row = [row_bot] + [""] * i
        row += [cells[(row_bot, col)] for col in bots[i:]]
        rows.append(row)

    if fmt == "tsv":
        return "\n".join("\t".join(row) for row in rows)
    if fmt == "csv":
        buffer = io.StringIO()
        csv.writer(buffer, lineterminator="\n").writerows(rows)
        return buffer.getvalue().rstrip("\n")
    if fmt == "md":
        lines = ["| " + " | ".join(header) + " |"]
        lines.append("|" + "---|" * len(header))
        for row in rows[1:]:
            lines.append("| " + " | ".join(row) + " |")
        return "\n".join(lines)
    raise ValueError(f"unknown format: {fmt}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Render the proven outcome matrix.")
    parser.add_argument("--format", choices=["tsv", "csv", "md"], default="tsv")
    parser.add_argument("--missing", default="Open Problem", help="cell text for unproven pairs")
    parser.add_argument(
        "--annotate",
        action="store_true",
        help="mark ∃k (existential budget) and k≫ (large-k threshold) theorem shapes",
    )
    parser.add_argument("--output", type=Path, default=None, help="write to file instead of stdout")
    args = parser.parse_args()

    bots, cells = build_outcome_matrix(missing=args.missing, annotate=args.annotate)
    rendered = format_matrix(bots, cells, fmt=args.format)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(rendered)


if __name__ == "__main__":
    main()

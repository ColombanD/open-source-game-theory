"""Outcome matrix from the proven theorem library.

Scans `engine/PrisonersDilemma/Theorems/**/*.lean` for the unified
`outcome_Bot1_vs_Bot2` / `llm_outcome_Bot1_vs_Bot2` theorems and renders an
upper-triangular matrix of proven outcomes. Purely static — no LLM, no Lean
invocation; the Lean kernel already checked every cell.

Acceptance rules (matching the tracking sheet's conventions):
- The matrix rows/columns are exactly the bot directories under `Theorems/`
  (so no `PrudentBot2`/`JustBot2` tier variants, no `OptimBot`).
- Only theorems named exactly `outcome_<A>_vs_<B>` or `llm_outcome_<A>_vs_<B>`
  with both `<A>` and `<B>` in that bot set are accepted — suffixed regime
  variants (`_floor`, `_floor2`, `_defended`, `_k<N>`) are ignored: the cell
  must be the large-`k` / unconditional statement.
- A theorem proved under extra side hypotheses (floor/size/budget guards,
  binders named `h…`) still fills the cell but is flagged with `†`.
- `= none` theorems render as `None` (provably no outcome).
- Cells with no accepted theorem come from `app/outcome_status.toml`
  (`Open Problem` / `Tried`) and are otherwise left empty.

Run with:
    uv run python -m pd_runner.eval.outcome_matrix
    uv run python -m pd_runner.eval.outcome_matrix --format md
    uv run python -m pd_runner.eval.outcome_matrix --format csv --output matrix.csv
    uv run python -m pd_runner.eval.outcome_matrix --push
"""

from __future__ import annotations

import argparse
import csv
import io
import logging
import re
import tomllib
from dataclasses import dataclass
from pathlib import Path

logger = logging.getLogger(__name__)


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_THEOREMS_DIR = _workspace_root() / "engine" / "PrisonersDilemma" / "Theorems"
_STATUS_FILE = _workspace_root() / "app" / "outcome_status.toml"

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

# Strict name match: bot names are alphanumeric (no underscores), so suffixed
# variants like `outcome_WaryBot_vs_DefectBot_floor` fail the `[({\[:]` boundary
# right after `<B>` and are skipped. Membership of <A>/<B> in the bot-directory
# set is enforced separately in `scan_outcome_theorems`.
_THEOREM_RE = re.compile(
    r"theorem\s+((llm_)?outcome_([A-Za-z0-9]+)_vs_([A-Za-z0-9]+))\s*[({\[:].*?:=",
    re.DOTALL,
)
_PAIR_RE = re.compile(r"=\s*some\s*\(\s*\.([CD])\s*,\s*\.([CD])\s*\)")
_NONE_RE = re.compile(r"=\s*none\b")
# Side-hypothesis binders follow the codebase convention of `h`-prefixed names
# ((hsz : …), (hjk : …), (hk : 2 ≤ k)); plain budget/fuel binders never do.
_HYP_RE = re.compile(r"\(\s*h\w*\s*:")


@dataclass(frozen=True)
class OutcomeTheorem:
    name: str
    left_bot: str
    right_bot: str
    # ("C", "D") for a proven action pair, None for a proven no-outcome.
    pair: tuple[str, str] | None
    # "universal" | "existential" (∃k) | "threshold" (∃k₂, ∀k>k₂) | "no_outcome"
    shape: str
    # Proved under extra side hypotheses (floor/size/budget guards).
    has_hypotheses: bool
    file: str


def library_bots(theorems_dir: Path = _THEOREMS_DIR) -> set[str]:
    """The bot set = per-bot theorem directories (may be empty placeholders).

    Only `LlmGenerations` (shared LLM lemmas, not a bot) is excluded.
    """
    return {
        d.name
        for d in theorems_dir.iterdir()
        if d.is_dir() and d.name != "LlmGenerations"
    }


def scan_outcome_theorems(theorems_dir: Path = _THEOREMS_DIR) -> list[OutcomeTheorem]:
    """Collect every accepted `(llm_)outcome_X_vs_Y` theorem with its result."""
    bots = library_bots(theorems_dir)
    theorems: list[OutcomeTheorem] = []
    for lean_file in sorted(theorems_dir.rglob("*.lean")):
        content = lean_file.read_text(encoding="utf-8")
        for match in _THEOREM_RE.finditer(content):
            name, left, right = match.group(1), match.group(3), match.group(4)
            if left not in bots or right not in bots:
                continue  # tier variants (JustBot2, …) or non-library opponents
            statement = match.group(0)

            pair_match = _PAIR_RE.search(statement)
            if pair_match:
                pair: tuple[str, str] | None = (pair_match.group(1), pair_match.group(2))
                if "∀" in statement and "∃" in statement:
                    shape = "threshold"
                elif "∃" in statement:
                    shape = "existential"
                else:
                    shape = "universal"
            elif _NONE_RE.search(statement):
                pair, shape = None, "no_outcome"
            else:
                continue  # not an outcome statement (e.g. helper with a lookalike name)

            theorems.append(OutcomeTheorem(
                name, left, right, pair, shape,
                has_hypotheses=bool(_HYP_RE.search(statement)),
                file=lean_file.name,
            ))
    return theorems


def load_status(
    status_file: Path = _STATUS_FILE,
    bots: set[str] | None = None,
) -> dict[tuple[str, str], str]:
    """Curated statuses for unproven cells, keyed by sorted (unordered) pair.

    The TOML file holds `[[open]]` / `[[tried]]` / `[[rework]]` tables with a
    `pair` array (and a free-form `reason`, kept for humans, ignored here).
    When a pair appears in several sections the strongest wins:
    open > rework > tried (so confirming a "Tried" pair as open needs no
    file surgery — just append the `[[open]]` entry).
    """
    if not status_file.exists():
        return {}
    data = tomllib.loads(status_file.read_text(encoding="utf-8"))
    statuses: dict[tuple[str, str], str] = {}
    for section, label in (("tried", "Tried"), ("rework", "Need rework"), ("open", "Open Problem")):
        for entry in data.get(section, []):
            pair = entry.get("pair", [])
            if len(pair) != 2:
                raise ValueError(f"{status_file.name}: [[{section}]] entry needs pair = [A, B], got {pair!r}")
            if bots is not None:
                unknown = [b for b in pair if b not in bots]
                if unknown:
                    raise ValueError(f"{status_file.name}: unknown bot(s) {unknown} in [[{section}]] {pair}")
            statuses[tuple(sorted(pair))] = label
    return statuses


def append_status(
    section: str,
    pair: tuple[str, str],
    reason: str,
    status_file: Path = _STATUS_FILE,
) -> bool:
    """Append a curated status entry to the TOML file.

    Returns False without writing when the pair is already recorded in the
    same section, or (for "tried", the weakest status) anywhere at all —
    a failed attempt never downgrades an existing open/rework verdict.
    """
    if section not in ("open", "tried", "rework"):
        raise ValueError(f"unknown status section: {section!r}")
    key = tuple(sorted(pair))
    if status_file.exists():
        data = tomllib.loads(status_file.read_text(encoding="utf-8"))
        for sec in ("open", "tried", "rework"):
            for entry in data.get(sec, []):
                if tuple(sorted(entry.get("pair", []))) == key and (sec == section or section == "tried"):
                    return False
    reason_safe = reason.replace("\\", "\\\\").replace('"', '\\"')
    entry = f'\n[[{section}]]\npair = ["{pair[0]}", "{pair[1]}"]\nreason = "{reason_safe}"\n'
    with status_file.open("a", encoding="utf-8") as fh:
        fh.write(entry)
    logger.info("outcome_status: recorded %s vs %s as [[%s]]", pair[0], pair[1], section)
    return True


def _bot_order(bots: set[str]) -> list[str]:
    ordered = [b for b in _CANONICAL_ORDER if b in bots]
    ordered += sorted(bots - set(ordered))
    return ordered


def build_outcome_matrix(
    theorems_dir: Path = _THEOREMS_DIR,
    status_file: Path | None = _STATUS_FILE,
    annotate: bool = False,
) -> tuple[list[str], dict[tuple[str, str], str]]:
    """Upper-triangular matrix of proven outcomes.

    Returns (bot order, cells) where cells maps (row_bot, col_bot) with
    row index ≤ column index to a rendered value. A cell reads from the row
    bot's perspective: (row's action, column's action). When only the
    reversed theorem exists, its pair is swapped to fit.
    """
    theorems = scan_outcome_theorems(theorems_dir)
    bots = library_bots(theorems_dir)
    statuses = load_status(status_file, bots) if status_file is not None else {}

    by_pair: dict[tuple[str, str], OutcomeTheorem] = {}
    for t in theorems:
        key = (t.left_bot, t.right_bot)
        # When a pair has both an `llm_outcome_` and a plain theorem, prefer plain.
        if key in by_pair and t.name.startswith("llm_"):
            continue
        by_pair[key] = t

    def render(t: OutcomeTheorem, swapped: bool) -> str:
        if t.pair is None:
            return "None"
        a, b = (t.pair[1], t.pair[0]) if swapped else t.pair
        cell = f"({a}, {b})"
        if t.has_hypotheses:
            cell += " †"
        if annotate and t.shape == "existential":
            cell += " ∃k"
        elif annotate and t.shape == "threshold":
            cell += " k≫"
        return cell

    cells: dict[tuple[str, str], str] = {}
    order = _bot_order(bots)
    for i, row in enumerate(order):
        for col in order[i:]:
            status = statuses.get(tuple(sorted((row, col))))
            if (row, col) in by_pair:
                cells[(row, col)] = render(by_pair[(row, col)], swapped=False)
            elif (col, row) in by_pair:
                cells[(row, col)] = render(by_pair[(col, row)], swapped=True)
            else:
                cells[(row, col)] = status or ""
                continue
            if status:
                logger.warning(
                    "outcome_status: %s vs %s is listed %r but has a proven theorem — "
                    "the proof wins; drop the stale status entry.", row, col, status,
                )
    return order, cells


def matrix_rows(bots: list[str], cells: dict[tuple[str, str], str]) -> list[list[str]]:
    """Header + one row per bot, upper-triangular (lower cells empty)."""
    rows = [["Outcome Matrix", *bots]]
    for i, row_bot in enumerate(bots):
        row = [row_bot] + [""] * i
        row += [cells[(row_bot, col)] for col in bots[i:]]
        rows.append(row)
    return rows


def format_matrix(
    bots: list[str],
    cells: dict[tuple[str, str], str],
    fmt: str = "tsv",
) -> str:
    rows = matrix_rows(bots, cells)
    if fmt == "tsv":
        return "\n".join("\t".join(row) for row in rows)
    if fmt == "csv":
        buffer = io.StringIO()
        csv.writer(buffer, lineterminator="\n").writerows(rows)
        return buffer.getvalue().rstrip("\n")
    if fmt == "md":
        header = rows[0]
        lines = ["| " + " | ".join(header) + " |"]
        lines.append("|" + "---|" * len(header))
        for row in rows[1:]:
            lines.append("| " + " | ".join(row) + " |")
        return "\n".join(lines)
    raise ValueError(f"unknown format: {fmt}")


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    parser = argparse.ArgumentParser(description="Render the proven outcome matrix.")
    parser.add_argument("--format", choices=["tsv", "csv", "md"], default="tsv")
    parser.add_argument(
        "--annotate",
        action="store_true",
        help="mark ∃k (existential budget) and k≫ (large-k threshold) theorem shapes",
    )
    parser.add_argument("--output", type=Path, default=None, help="write to file instead of stdout")
    parser.add_argument("--push", action="store_true", help="push the matrix to the Google Sheet")
    args = parser.parse_args()

    if args.push:
        from pd_runner.services.sheets import SheetsPushError, push_matrix

        try:
            summary = push_matrix(annotate=args.annotate)
        except SheetsPushError as exc:
            raise SystemExit(f"error: {exc}")
        print(f"pushed {summary['bots']}×{summary['bots']} matrix to "
              f"worksheet {summary['worksheet']!r}: {summary['proven']} proven, "
              f"{summary['none']} None, {summary['open']} open, "
              f"{summary['rework']} need rework, {summary['tried']} tried, "
              f"{summary['empty']} empty")
        print(summary["spreadsheet_url"])
        return

    bots, cells = build_outcome_matrix(annotate=args.annotate)
    rendered = format_matrix(bots, cells, fmt=args.format)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(rendered)


if __name__ == "__main__":
    main()

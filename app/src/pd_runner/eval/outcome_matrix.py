"""Outcome matrix from the proven theorem library.

The cells come from the Lean-side `@[outcome]` export: `lake exe export_outcomes`
inspects the ELABORATED TYPE of every tagged theorem (`Outcome/Lint.lean`) and writes
`app/generated/outcome_theorems.json`; this module reads that file and renders an
upper-triangular matrix. No LLM, no regex over Lean source; the kernel checked every
cell and the linter checked that each statement is on the `OutcomeSpec` template and
agrees with its own name.

Acceptance rules (matching the tracking sheet's conventions):
- The matrix rows/columns are exactly the bot directories under `Theorems/`
  (so no `PrudentBot2`/`JustBot2` tier variants).
- A cell is filled only by an `@[outcome]`-tagged theorem. Tagging is opt-in; the
  build-time census (`Outcome/Check.lean`) is what turns a forgotten tag into a
  build failure rather than a silently open-looking cell.
- A theorem is flagged `†` when the export says it is STAGGERED (a bot applied to a
  budget expression other than the shared `k`, e.g. `PrudentBot (2*k+64)`) or carries
  a SIDE CONDITION (a `Prop` binder in the telescope). Budget floors are
  not caveats: they are the `.eventual` regime and carry no dagger.
- `= none` theorems render as `None` (provably no outcome).
- Cells with no accepted theorem come from `app/outcome_status.toml`
  (`Open Problem` / `Tried`) and are otherwise left empty.

FRESHNESS. The export is a committed artifact, so the matrix is only as current as
the last `lake exe export_outcomes`. `export_staleness()` detects a lagging file and
`refresh_export()` regenerates it (build + export); the library writer refreshes it
after every accepted proof and the web UI exposes the check and the button.

Run with:
    uv run python -m pd_runner.eval.outcome_matrix
    uv run python -m pd_runner.eval.outcome_matrix --format md
    uv run python -m pd_runner.eval.outcome_matrix --format csv --output matrix.csv
    uv run python -m pd_runner.eval.outcome_matrix --refresh        # rebuild the export first
    uv run python -m pd_runner.eval.outcome_matrix --push
    uv run python -m pd_runner.eval.outcome_matrix --prune-stale --push
"""

from __future__ import annotations

import argparse
import csv
import io
import logging
import json
import re
import subprocess
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





@dataclass(frozen=True)
class OutcomeTheorem:
    name: str
    left_bot: str
    right_bot: str
    # ("C", "D") for a proven action pair, None for a proven no-outcome.
    pair: tuple[str, str] | None
    # "universal" | "threshold" (∃k₂, ∀k>k₂) | "no_outcome".
    # ("existential" (∃k) is retained in the vocabulary but no longer produced: every
    # `∃ k` theorem was strengthened during the OutcomeSpec migration.)
    shape: str
    # Proved under extra side hypotheses (floor/size/budget guards).
    has_hypotheses: bool
    file: str
    # --- Lean-export-only fields (additive; empty for legacy regex-scanned rows) ---
    # The `BudgetRegime` the theorem was stated in: nobudget | universal | eventual.
    # Richer than `shape`, which is kept lossy for backward compatibility.
    budget_regime: str = ""
    # `outcome (fuel + pad)` — the cofinite fuel offset.
    fuel_pad: int = 0
    # The defining module, e.g. `PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot`.
    module: str = ""


def library_bots(theorems_dir: Path = _THEOREMS_DIR) -> set[str]:
    """The bot set = per-bot theorem directories (may be empty placeholders).

    Only `LlmGenerations` (shared LLM lemmas, not a bot) is excluded.
    """
    return {
        d.name
        for d in theorems_dir.iterdir()
        if d.is_dir() and d.name != "LlmGenerations"
    }


# The Lean-side export (`lake exe export_outcomes`) — structured data recovered from
# ELABORATED TYPES, so the regime and the side conditions are read rather than guessed.
# Committed so the Python side works without a Lean toolchain; `source_digest` lets the
# Lean linter reject a stale or hand-edited file.
_EXPORT_FILE = Path(__file__).resolve().parents[3] / "generated" / "outcome_theorems.json"

# `BudgetRegime` -> the legacy `shape` vocabulary. Deliberately lossy in exactly the way
# the regex classifier was, so `tau/matrix.py` and the tau tests are unaffected.
# NOTE: "existential" is now unreachable (the `witness` regime collapsed into `eventual`);
# it stays in the vocabulary only for `outcome_status.toml` history.
_SHAPE_MAP = {
    "nobudget": "universal",
    "universal": "universal",
    "eventual": "threshold",
}


def _fnv1a64(text: str) -> int:
    """FNV-1a, mirroring `PD.Outcome.digestOf` in `Outcome/Export.lean`."""
    h = 1469598103934665603
    for ch in text:
        h = ((h ^ ord(ch)) * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    return h


def _verify_digest(data: dict, export_file: Path) -> None:
    """Reject a hand-edited export.

    The cells are machine-checked THEOREMS; a JSON someone edited by hand is not. Without
    this check, flipping a `pair` in the file silently rewrites a proven matrix cell and
    every downstream consumer believes it.
    """
    claimed = data.get("source_digest")
    if claimed is None:
        raise ValueError(f"{export_file}: missing `source_digest`")
    rows = [
        json.dumps(t, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        for t in data["theorems"]
    ]
    actual = str(_fnv1a64("".join(rows)))
    if actual != claimed:
        raise ValueError(
            f"{export_file}: source_digest mismatch — the file was edited by hand or is "
            f"stale (claimed {claimed}, recomputed {actual}). Regenerate it with "
            f"`lake exe export_outcomes`; never hand-edit proven cells."
        )


def _theorems_from_export(export_file: Path = _EXPORT_FILE) -> list[OutcomeTheorem]:
    """Read the `@[outcome]` cells exported from Lean.

    Returns [] when the file is absent, so a partially-migrated tree still works: during
    the migration `scan_outcome_theorems` unions this with the legacy regex scan.
    """
    if not export_file.exists():
        return []
    data = json.loads(export_file.read_text(encoding="utf-8"))
    version = data.get("schema_version")
    if version != 1:
        raise ValueError(
            f"{export_file}: unsupported schema_version {version!r} (expected 1)"
        )
    _verify_digest(data, export_file)
    out: list[OutcomeTheorem] = []
    for t in data["theorems"]:
        pair = tuple(t["pair"]) if t["pair"] else None
        shape = "no_outcome" if pair is None else _SHAPE_MAP[t["budget_regime"]]
        out.append(OutcomeTheorem(
            name=t["name"],
            left_bot=t["left_bot"],
            right_bot=t["right_bot"],
            pair=pair,
            shape=shape,
            # One flag, two honest causes: a real `Prop` binder, or a staggered budget.
            has_hypotheses=bool(t["side_conditions"]) or bool(t["staggered"]),
            file=t.get("file", ""),
            budget_regime=t["budget_regime"],
            fuel_pad=t["fuel_pad"],
            module=t.get("module", ""),
        ))
    return out


def export_staleness(
    export_file: Path = _EXPORT_FILE,
    theorems_dir: Path = _THEOREMS_DIR,
) -> str | None:
    """Why the committed export may be BEHIND the Lean sources, or None if it is not.

    The digest catches a tampered file and the Lean census catches an untagged theorem;
    neither notices an export that is merely stale (tag a theorem, skip the export, and
    the matrix keeps serving the previous cell set). Anchored on the source tree rather
    than a counter: `@[outcome]` occurrences under `Theorems/` are exactly what the
    export enumerates, so the two counts must agree. A count match is not proof of
    freshness (a statement edited in place keeps the count), which is why the hard
    check is paired with a modification-time hint.
    """
    if not export_file.exists():
        return "outcome_theorems.json is missing — run `lake exe export_outcomes`"
    if not theorems_dir.is_dir():
        return None  # app-only checkout: nothing to compare against
    tagged_on_disk = 0
    newest_source = 0.0
    for f in theorems_dir.rglob("vs_*.lean"):
        tagged_on_disk += f.read_text(encoding="utf-8").count("@[outcome]")
        newest_source = max(newest_source, f.stat().st_mtime)
    exported = len(json.loads(export_file.read_text(encoding="utf-8"))["theorems"])
    if exported != tagged_on_disk:
        return (
            f"export has {exported} cells but {tagged_on_disk} theorems are tagged "
            f"`@[outcome]` on disk — regenerate it"
        )
    if newest_source > export_file.stat().st_mtime:
        return "a theorem file is newer than the export — regenerate it to be sure"
    return None


def refresh_export(
    engine_dir: Path | None = None,
    export_file: Path = _EXPORT_FILE,
) -> str:
    """Regenerate the export from the Lean sources. Returns the exporter's stdout.

    Two steps, both required: `lake exe export_outcomes` reads the BUILT `.olean`s
    (it imports `PrisonersDilemma` at runtime rather than depending on it), so running
    it against stale oleans would silently export the previous library. Building
    `OutcomeCheck` alongside the engine also runs the validator + census, so an
    off-template or untagged theorem fails here instead of vanishing from the matrix.
    Raises `RuntimeError` with the tool output on failure.
    """
    if engine_dir is None:
        engine_dir = _workspace_root() / "engine"
    for cmd in (
        ["lake", "build", "PrisonersDilemma", "OutcomeCheck"],
        ["lake", "exe", "export_outcomes", str(export_file.resolve())],
    ):
        proc = subprocess.run(cmd, cwd=engine_dir, capture_output=True, text=True, check=False)
        if proc.returncode != 0:
            raise RuntimeError(
                f"`{' '.join(cmd)}` failed (exit {proc.returncode}):\n"
                f"{proc.stdout[-4000:]}\n{proc.stderr[-4000:]}"
            )
    logger.info("outcome export refreshed: %s", proc.stdout.strip())
    return proc.stdout


def scan_outcome_theorems(
    theorems_dir: Path | None = None,
    export_file: Path = _EXPORT_FILE,
) -> list[OutcomeTheorem]:
    """Every accepted `(llm_)outcome_X_vs_Y` theorem with its result.

    Read entirely from the Lean-side `@[outcome]` export: the shape, the fuel mode, the
    side conditions and the staggering are recovered from ELABORATED TYPES, not guessed
    from source text. The regex extractor this replaced inferred the dagger from
    "does a binder name start with `h`", which silently mis-classified at least one cell.

    `theorems_dir` is accepted and IGNORED. It survives because callers pair this with
    `library_bots(theorems_dir)`, which genuinely does read the directory listing; taking
    the argument keeps those call sites symmetric. Point `export_file` at a different
    JSON to scan an alternative library.
    """
    del theorems_dir  # the export, not the source tree, is the authority
    return sorted(_theorems_from_export(export_file), key=lambda t: t.name)


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


_ENTRY_HEADER_RE = re.compile(r"^\[\[(open|tried|rework)\]\]\s*$")
_ENTRY_PAIR_RE = re.compile(r'pair\s*=\s*\[\s*"([^"]+)"\s*,\s*"([^"]+)"\s*\]')


def prune_stale_statuses(
    status_file: Path = _STATUS_FILE,
    theorems_dir: Path = _THEOREMS_DIR,
) -> list[tuple[str, str, str]]:
    """Delete status entries whose (unordered) pair has an accepted theorem.

    The proof always wins at render time; this removes the stale TOML entries
    the render-time warning nags about. Only the matching `[[section]]` blocks
    are dropped — comment banners and every other line survive byte-for-byte.
    Returns the removed (section, botA, botB) triples, empty when nothing was
    stale.
    """
    if not status_file.exists():
        return []
    proven = {
        tuple(sorted((t.left_bot, t.right_bot)))
        for t in scan_outcome_theorems(theorems_dir)
    }
    lines = status_file.read_text(encoding="utf-8").splitlines(keepends=True)
    kept: list[str] = []
    removed: list[tuple[str, str, str]] = []
    i = 0
    while i < len(lines):
        header = _ENTRY_HEADER_RE.match(lines[i])
        if not header:
            kept.append(lines[i])
            i += 1
            continue
        # The entry block: `key = value` lines and blank separators after the
        # header, stopping at the next table header or a comment banner (those
        # belong to the file, not the entry).
        j = i + 1
        while (
            j < len(lines)
            and not _ENTRY_HEADER_RE.match(lines[j])
            and not lines[j].lstrip().startswith("#")
            and (lines[j].strip() == "" or "=" in lines[j])
        ):
            j += 1
        block = lines[i:j]
        pair_match = _ENTRY_PAIR_RE.search("".join(block))
        if pair_match and tuple(sorted(pair_match.groups())) in proven:
            removed.append((header.group(1), pair_match.group(1), pair_match.group(2)))
            logger.info(
                "outcome_status: pruned stale [[%s]] %s vs %s (proven theorem exists)",
                header.group(1), pair_match.group(1), pair_match.group(2),
            )
        else:
            kept.extend(block)
        i = j
    if removed:
        status_file.write_text("".join(kept), encoding="utf-8")
    return removed


def index_by_ordered_pair(
    theorems: list[OutcomeTheorem],
) -> dict[tuple[str, str], OutcomeTheorem]:
    """Index accepted theorems by their ORDERED (left, right) pair.

    When a pair has both an `llm_outcome_` and a hand-written theorem, the
    hand-written one wins. Shared with `pd_runner.tau`, which needs the same
    acceptance policy but its own (ordered, not triangular) orientation.
    """
    by_pair: dict[tuple[str, str], OutcomeTheorem] = {}
    for t in theorems:
        key = (t.left_bot, t.right_bot)
        if key in by_pair and t.name.startswith("llm_"):
            continue
        by_pair[key] = t
    return by_pair


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

    by_pair = index_by_ordered_pair(theorems)

    def render(t: OutcomeTheorem, swapped: bool) -> str:
        if t.pair is None:
            return "None"
        a, b = (t.pair[1], t.pair[0]) if swapped else t.pair
        cell = f"({a}, {b})"
        if t.has_hypotheses:
            cell += " †"
        if annotate and t.shape == "threshold":
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
        help="mark k≫ (large-k threshold) theorem shapes",
    )
    parser.add_argument("--output", type=Path, default=None, help="write to file instead of stdout")
    parser.add_argument(
        "--refresh",
        action="store_true",
        help="rebuild the Lean export (lake build + lake exe export_outcomes) before rendering",
    )
    parser.add_argument("--push", action="store_true", help="push the matrix to the Google Sheet")
    parser.add_argument(
        "--prune-stale",
        action="store_true",
        help="delete outcome_status.toml entries whose pair now has an accepted theorem",
    )
    args = parser.parse_args()

    if args.refresh:
        try:
            print(refresh_export().strip())
        except RuntimeError as exc:
            raise SystemExit(f"error: {exc}")
    elif (stale := export_staleness()) is not None:
        logger.warning("outcome export may be stale: %s (use --refresh)", stale)

    if args.prune_stale:
        removed = prune_stale_statuses()
        if removed:
            for section, a, b in removed:
                print(f"pruned stale [[{section}]] {a} vs {b}")
        else:
            print("no stale status entries")

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

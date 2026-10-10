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
- A cell is flagged `†` iff the export says it is STAGGERED: a bot applied to a
  budget other than the shared `k` (`LegibleBot (2*k+64) k`, a free `(j : Nat)`, a
  literal), i.e. no shared-budget theorem exists for the pair. That is the dagger's
  only cause — the linter rejects side hypotheses outright, and budget floors are the
  `.eventual` regime, not caveats.
- A cell is BUDGET-SENSITIVE, rendered `(D, D) ⇄ (C, C)`, when a `@[outcome_companion]`
  theorem (`…_staggered`, the same pair with one bot at a bigger budget) proves a
  DIFFERENT outcome: the first pair is the shared-budget cell, the second what the
  pair does once a budget stagger is allowed. Both are theorems; the mark keeps the
  staggered result visible instead of losing it when the cell moved to the shared
  budget (2026-08-27). A companion agreeing with its cell adds no mark.
- `= none` theorems render as `None` (provably no outcome).
- Cells with no accepted theorem come from `app/outcome_status.toml`
  (`Open Problem` / `Tried`) and are otherwise left empty.

FRESHNESS. The export is a committed artifact, so the matrix is only as current as
the last `lake exe export_outcomes`. `export_staleness()` detects a lagging file and
`refresh_export()` regenerates it (build + export); the library writer refreshes it
after every accepted proof and the web UI exposes the check and the button.

TWO SOURCES (2026-09-30, `Research/Notes/SPRIME_SOURCE_OF_TRUTH.md`). The cells above
describe the engine's stipulated `S`. The arithmetized system PA-`S'` (`arith/`) re-proves
the matrix cell by cell and exports it to `app/generated/sprime_outcome_theorems.json`
(`lake exe export_sprime_outcomes`) in the SAME schema plus `"system": "sprime"` and a
`floors` array. `S'` is the DEFAULT source (`settings.CELL_SOURCE`, env `PD_CELL_SOURCE`);
the engine stays loadable as the comparison (`source="engine"`). Under `S'`:
- a cell is `provenance="sprime"` (a kernel-checked `@[outcomeA]` theorem), or
- `provenance="floor_dichotomy"` (`‡`): a GENUINE FLOOR — the pair's value hinges on
  bounded consistency of `TAct` at `k`; `S'` proves the hypothesis-free dichotomy
  `dich_<L>_vs_<R>` and the cell carries the engine-side (`¬A_k`) value under
  `FloorPolicy.engine_side` (the default) or is a HOLE under `restrict_zoo`;
- a cell marked `≠` FLIPS the engine: `S'` proves a different value than `S` (all
  nine in-paper flips are DIMCID's — `S'` reads every source, `S` does not).
The engine path is byte-identical to before the switch (`tests/test_cell_source.py`).
A missing `S'` export is an ERROR, not an empty matrix (`PD_SPRIME_EXPORT` points the
loader at an alternative document; the test-suite uses it for its sample).

Run with:
    uv run python -m pd_runner.eval.outcome_matrix
    uv run python -m pd_runner.eval.outcome_matrix --source engine
    uv run python -m pd_runner.eval.outcome_matrix --format md
    uv run python -m pd_runner.eval.outcome_matrix --format csv --output matrix.csv
    uv run python -m pd_runner.eval.outcome_matrix --refresh        # rebuild the export first
    uv run python -m pd_runner.eval.outcome_matrix --push
    uv run python -m pd_runner.eval.outcome_matrix --prune-stale --push
    uv run python -m pd_runner.eval.source_diff                     # engine vs S' report
"""

from __future__ import annotations

import argparse
import csv
import io
import logging
import json
import re
import subprocess
import os
import tomllib
from dataclasses import dataclass
from dataclasses import replace as dataclass_replace
from pathlib import Path

from pd_runner import settings
from pd_runner.settings import CellSource, resolve_floor_policy, resolve_source

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
class Companion:
    """A `@[outcome_companion]` theorem: the cell's pair under a budget stagger."""
    name: str
    left_bot: str
    right_bot: str
    pair: tuple[str, str] | None
    # The staggered bot arguments as Lean text, e.g. `fun k => PrudentBot (2 * k + 64)`.
    left: str
    right: str
    budget_regime: str = ""
    fuel_pad: int = 0

    def oriented_pair(self, left_bot: str) -> tuple[str, str] | None:
        """The companion's pair read from `left_bot`'s side."""
        if self.pair is None:
            return None
        return self.pair if self.left_bot == left_bot else (self.pair[1], self.pair[0])


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
    # The dagger: a bot runs at a budget other than the shared `k` (see module doc).
    staggered: bool
    file: str
    # --- Lean-export-only fields (additive; empty for legacy regex-scanned rows) ---
    # The `BudgetRegime` the theorem was stated in: nobudget | universal | eventual.
    # Richer than `shape`, which is kept lossy for backward compatibility.
    budget_regime: str = ""
    # `outcome (fuel + pad)` — the cofinite fuel offset.
    fuel_pad: int = 0
    # The defining module, e.g. `PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot`.
    module: str = ""
    # Staggered companions of this pair (either orientation), from the export.
    companions: tuple[Companion, ...] = ()
    # The two bot arguments as text (`PrudentBot (2 * k + 64)`, `DupocBot k`, `DefectBot`).
    left_text: str = ""
    right_text: str = ""
    # --- Source provenance (2026-09-30) ---
    # `engine` (an `@[outcome]` theorem of the stipulated `S`), `sprime` (an `@[outcomeA]`
    # theorem of PA-`S'`), or `floor_dichotomy` (the engine-side half of a `S'` floor
    # dichotomy, carried as a cell under `FloorPolicy.engine_side`).
    provenance: str = "engine"
    # Floors only: the hinge `A_k` (pretty text) the cell's value is conditional on —
    # `¬A_k` gives this cell's value, `A_k` the other branch of the dichotomy.
    hinge: str = ""
    # Floors only: the hypothesis-free dichotomy theorem, `dich_<L>_vs_<R>`.
    dichotomy: str = ""
    # Floors only: WHICH branch of the dichotomy `pair` is — `"engine_side"` (`¬A_k`, the
    # exported value) or `"hinge_side"` (`A_k`, `sprime_floors.HINGE_SIDE_PAIRS`), i.e.
    # the `FloorPolicy` the cell was read under. Empty for a theorem.
    floor_branch: str = ""
    # `S'` only: the hand-template TWIN name(s) the exported statement was on before
    # `SPRIME_TWIN_BASE` aliased `left_bot`/`right_bot` to the engine bot (`"Just7"`,
    # or `"Just7, Dupoc"` when both sides were twins); `name` stays as exported.
    twin_of: str = ""

    @property
    def is_floor(self) -> bool:
        return self.provenance == "floor_dichotomy"

    @property
    def budget_sensitive(self) -> bool:
        """Some staggered companion proves a DIFFERENT outcome than the cell."""
        return any(
            c.oriented_pair(self.left_bot) != self.pair for c in self.companions
        )


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
# The PA-`S'` export (`arith/`, `lake exe export_sprime_outcomes`), same schema plus
# `system`/`provenance`/`floors`. `PD_SPRIME_EXPORT` points the loader at an alternative
# document (the test-suite uses it for its ledger-derived sample while the real export
# has not been generated yet); it never applies to the engine file.
_SPRIME_EXPORT_FILE = Path(
    os.getenv("PD_SPRIME_EXPORT")
    or Path(__file__).resolve().parents[3] / "generated" / "sprime_outcome_theorems.json"
)
# One export per `CellSource`. Consulted at CALL time (never captured as a default
# argument), so pointing a source elsewhere is one dict assignment.
_EXPORT_FILES: dict[CellSource, Path] = {
    "engine": _EXPORT_FILE,
    "sprime": _SPRIME_EXPORT_FILE,
}
# The `S'` sources the sprime export is anchored on (staleness by mtime + tag count).
_ARITH_DIR = _workspace_root() / "arith"
_SPRIME_OUTCOME_DIR = _ARITH_DIR / "ArithS" / "Outcome"
_SPRIME_FLOOR_FILE = _ARITH_DIR / "ArithS" / "Cells" / "FloorDichotomy.lean"
# The tau twin (`Tau/RowSpec.lean` rows), written by the same exporter; read by
# `tau/def4_theorems.py`.
_TAU_EXPORT_FILE = Path(__file__).resolve().parents[3] / "generated" / "tau_rows.json"
_TAU_PHASE_DIR = _workspace_root() / "engine" / "PrisonersDilemma" / "Tau" / "Theorems"


def export_file_for(source: str | None = None) -> Path:
    """The export document a `CellSource` reads (default: `settings.CELL_SOURCE`)."""
    return _EXPORT_FILES[resolve_source(source)]

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


def _verify_digest(data: dict, export_file: Path, key: str = "theorems") -> None:
    """Reject a hand-edited export.

    The cells are machine-checked THEOREMS; a JSON someone edited by hand is not. Without
    this check, flipping a `pair` in the file silently rewrites a proven matrix cell and
    every downstream consumer believes it.
    """
    claimed = data.get("source_digest")
    if claimed is None:
        raise ValueError(f"{export_file}: missing `source_digest`")
    # The engine hashes `theorems ++ companions`; a `S'` document hashes
    # `theorems ++ companions ++ floors`, in that order (`ArithS/Outcome/Export.lean`).
    hashed = data[key] + data.get("companions", [])
    if data.get("system") == "sprime":
        hashed = hashed + data.get("floors", [])
    rows = [
        json.dumps(t, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        for t in hashed
    ]
    actual = str(_fnv1a64("".join(rows)))
    if actual != claimed:
        exporter = ("lake exe export_sprime_outcomes" if data.get("system") == "sprime"
                    else "lake exe export_outcomes")
        raise ValueError(
            f"{export_file}: source_digest mismatch — the file was edited by hand or is "
            f"stale (claimed {claimed}, recomputed {actual}). Regenerate it with "
            f"`{exporter}`; never hand-edit proven cells."
        )


def _theorems_from_export(
    export_file: Path = _EXPORT_FILE,
    floor_policy: str | None = None,
) -> list[OutcomeTheorem]:
    """Read the `@[outcome]` (engine) or `@[outcomeA]`/`@[floorA]` (`S'`) cells exported
    from Lean.

    Returns [] when the file is absent (the engine's historical contract; `scan_outcome_
    theorems` turns an absent `S'` export into an error). A document with
    `"system": "sprime"` also carries `floors`: under `FloorPolicy.engine_side` they join
    the list as `provenance="floor_dichotomy"` cells holding the engine-side value; under
    `hinge_side` they join holding the OTHER branch (`sprime_floors.HINGE_SIDE_PAIRS`,
    `floor_branch="hinge_side"`); under `restrict_zoo` they are dropped (holes).
    `floor_policy` is ignored for an engine document, which has no floors.
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
    system = data.get("system", "engine")
    default_provenance = "sprime" if system == "sprime" else "engine"
    companions: dict[frozenset[str], list[Companion]] = {}
    for c in data.get("companions", []):
        comp = Companion(
            name=c["name"], left_bot=c["left_bot"], right_bot=c["right_bot"],
            pair=tuple(c["pair"]) if c["pair"] else None,
            left=c.get("left", ""), right=c.get("right", ""),
            budget_regime=c["budget_regime"], fuel_pad=c["fuel_pad"],
        )
        companions.setdefault(frozenset((c["left_bot"], c["right_bot"])), []).append(comp)
    def row(t: dict, provenance: str, floor_branch: str = "") -> OutcomeTheorem:
        pair = tuple(t["pair"]) if t["pair"] else None
        shape = "no_outcome" if pair is None else _SHAPE_MAP[t["budget_regime"]]
        return OutcomeTheorem(
            name=t["name"],
            left_bot=t["left_bot"],
            right_bot=t["right_bot"],
            pair=pair,
            shape=shape,
            staggered=bool(t["staggered"]),
            file=t.get("file", ""),
            budget_regime=t["budget_regime"],
            fuel_pad=t["fuel_pad"],
            module=t.get("module", ""),
            companions=tuple(companions.get(frozenset((t["left_bot"], t["right_bot"])), ())),
            left_text=t.get("left", ""),
            right_text=t.get("right", ""),
            provenance=provenance,
            hinge=t.get("hinge", ""),
            dichotomy=t.get("dichotomy", ""),
            floor_branch=floor_branch,
        )

    out = [row(t, t.get("provenance") or default_provenance) for t in data["theorems"]]
    policy = resolve_floor_policy(floor_policy)
    if system == "sprime" and policy in ("engine_side", "hinge_side"):
        for f in data.get("floors", []):
            if f["pair"] is None:
                raise ValueError(
                    f"{export_file}: floor {f['name']} has no engine-side value")
            if policy == "hinge_side":
                from pd_runner.eval.sprime_floors import hinge_side_pair

                f = {**f, "pair": list(hinge_side_pair(f.get("dichotomy", ""), f["name"]))}
            out.append(row(f, "floor_dichotomy", floor_branch=policy))
    if system == "sprime":
        out = _alias_sprime_twins(out, export_file)
    return out


# The `S'` HAND-TEMPLATE TWINS (`arith/ArithS/Agents/Template.lean`, `Cells/JustSlot`):
# bots whose route-(c) guard freezes a budget-carrying snapshot are stated on a
# constant-template twin that plays identically in every frame (`Just7`/`CupodTroll7`,
# the budget in template slot #6), and the Löb families are stated on the short names
# `Dupoc`/`Cupod`/`Just`. The exporter keeps the twin's name in `left_bot`/`right_bot`;
# the app reads the cell for the ENGINE bot. Never applied to the engine source.
#
# DORMANT since 2026-10-02: the last twin-named cells were re-proved on the engine's own
# `JustBot`/`CupodTrollBot` (`arith/ArithS/Cells/JustEngine.lean`, `CupodTrollEngine.lean`;
# the Dupoc/Cupod twins went on 2026-09-30), so `lake exe export_sprime_outcomes` writes no
# twin name and the aliasing never fires on the real export (`twin_of` is `""` on every
# row; `tests/test_cell_source.py` asserts it). The mechanism is kept so that an export
# from an older checkout still loads, and so that a twin sneaking back is aliased and
# collision-checked rather than surfacing as a sixteenth-plus bot.
SPRIME_TWIN_BASE: dict[str, str] = {
    "Just7": "JustBot",
    "Just": "JustBot",
    "Dupoc": "DupocBot",
    "Cupod": "CupodBot",
    "CupodTroll7": "CupodTrollBot",
}


def _alias_sprime_twins(
    theorems: list[OutcomeTheorem], export_file: Path,
) -> list[OutcomeTheorem]:
    """Rewrite twin-named `S'` rows onto their engine bots (`SPRIME_TWIN_BASE`),
    recording the twin in `twin_of`; `name` stays as exported.

    Collisions: when an aliased row lands on a pair another row (aliased or not)
    already states, the two must agree (read from one side); a disagreement is an
    ERROR (two `S'` theorems cannot prove different values for one engine pair —
    that would mean a twin is not a twin). On agreement the NON-aliased row is kept,
    and between two aliased rows the first. Rows on pairs nobody else states are
    simply renamed.
    """
    aliased: list[OutcomeTheorem] = []
    plain: list[OutcomeTheorem] = []
    for t in theorems:
        twins = [b for b in (t.left_bot, t.right_bot) if b in SPRIME_TWIN_BASE]
        if not twins:
            plain.append(t)
            continue
        aliased.append(dataclass_replace(
            t,
            left_bot=SPRIME_TWIN_BASE.get(t.left_bot, t.left_bot),
            right_bot=SPRIME_TWIN_BASE.get(t.right_bot, t.right_bot),
            twin_of=", ".join(dict.fromkeys(twins)),
        ))
    by_pair: dict[frozenset[str], OutcomeTheorem] = {}
    for t in plain:
        by_pair.setdefault(frozenset((t.left_bot, t.right_bot)), t)
    out = list(plain)
    for t in aliased:
        key = frozenset((t.left_bot, t.right_bot))
        other = by_pair.get(key)
        if other is None:
            by_pair[key] = t
            out.append(t)
            continue
        if oriented_pair(other, t.left_bot) != t.pair or other.is_floor != t.is_floor:
            raise ValueError(
                f"{export_file}: twin-aliased {t.name} ({t.twin_of} → "
                f"{t.left_bot} vs {t.right_bot}, {t.pair}) contradicts {other.name} "
                f"({oriented_pair(other, t.left_bot)}) for the same pair — a twin that "
                "is not a twin; fix the export, do not alias around it"
            )
        logger.debug("S' twin row %s agrees with %s; keeping the latter", t.name, other.name)
    return out


# An attribute on its own line — a docstring MENTIONING `@[outcome]` must not count.
_OUTCOME_TAG_RE = re.compile(r"^@\[outcome\]\s*$", re.MULTILINE)
_TAU_TAG_RE = re.compile(r"^@\[tau_row\]\s*$", re.MULTILINE)
_COMPANION_TAG_RE = re.compile(r"^@\[outcome_companion\]\s*$", re.MULTILINE)
# The `S'` tags (`ArithS/Outcome/Attr.lean`); at line start, `theorem` may follow on
# the same line.
_OUTCOMEA_TAG_RE = re.compile(r"^@\[outcomeA\]", re.MULTILINE)
_FLOORA_TAG_RE = re.compile(r"^@\[floorA\]", re.MULTILINE)


def _sprime_export_staleness(export_file: Path, outcome_dir: Path, floor_file: Path) -> str | None:
    """`export_staleness` for the `S'` export: the newest `.lean` under
    `arith/ArithS/Outcome/` (and `Cells/FloorDichotomy.lean`) against the export's mtime,
    plus the `@[outcomeA]`/`@[floorA]` tag counts when the Lean side carries them."""
    if not export_file.exists():
        return (f"{export_file.name} is missing — run `lake exe export_sprime_outcomes` "
                "in arith/ (or set PD_CELL_SOURCE=engine)")
    if not outcome_dir.is_dir():
        return None  # app-only checkout: nothing to compare against
    sources = list(outcome_dir.rglob("*.lean"))
    if floor_file.exists():
        sources.append(floor_file)
    data = json.loads(export_file.read_text(encoding="utf-8"))
    tagged_cells = sum(len(_OUTCOMEA_TAG_RE.findall(f.read_text(encoding="utf-8")))
                       for f in outcome_dir.rglob("*.lean"))
    tagged_floors = sum(len(_FLOORA_TAG_RE.findall(f.read_text(encoding="utf-8")))
                        for f in outcome_dir.rglob("*.lean"))
    exported = len(data.get("theorems", []))
    exported_floors = len(data.get("floors", []))
    # The tag census only applies once the Lean side is tagged at all (an export
    # generated elsewhere against an untagged checkout has nothing to count against).
    if tagged_cells and exported != tagged_cells:
        return (f"S' export has {exported} cells but {tagged_cells} theorems are tagged "
                "`@[outcomeA]` on disk — regenerate it (`lake exe export_sprime_outcomes`)")
    if tagged_floors and exported_floors != tagged_floors:
        return (f"S' export has {exported_floors} floors but {tagged_floors} theorems are "
                "tagged `@[floorA]` on disk — regenerate it (`lake exe export_sprime_outcomes`)")
    newest = max((f.stat().st_mtime for f in sources), default=0.0)
    if newest > export_file.stat().st_mtime:
        return ("an ArithS/Outcome source is newer than the S' export — regenerate it "
                "(`lake exe export_sprime_outcomes`) to be sure")
    return None


def export_staleness(
    export_file: Path | None = None,
    theorems_dir: Path = _THEOREMS_DIR,
    tau_export_file: Path = _TAU_EXPORT_FILE,
    tau_phase_dir: Path = _TAU_PHASE_DIR,
    *,
    source: str | None = None,
) -> str | None:
    """Why the committed export may be BEHIND the Lean sources, or None if it is not.

    The digest catches a tampered file and the Lean census catches an untagged theorem;
    neither notices an export that is merely stale (tag a theorem, skip the export, and
    the matrix keeps serving the previous cell set). Anchored on the source tree rather
    than a counter: `@[outcome]` occurrences under `Theorems/` are exactly what the
    export enumerates, so the two counts must agree. A count match is not proof of
    freshness (a statement edited in place keeps the count), which is why the hard
    check is paired with a modification-time hint.

    `source` picks the export (`settings.CELL_SOURCE` by default; an explicit
    `export_file` with no `source` is read as the ENGINE file, the historical calling
    convention). The `S'` check is `_sprime_export_staleness`.
    """
    resolved = resolve_source(source) if (source is not None or export_file is None) else "engine"
    if resolved == "sprime":
        return _sprime_export_staleness(
            export_file or _EXPORT_FILES["sprime"], _SPRIME_OUTCOME_DIR, _SPRIME_FLOOR_FILE)
    if export_file is None:
        export_file = _EXPORT_FILES["engine"]
    if not export_file.exists():
        return "outcome_theorems.json is missing — run `lake exe export_outcomes`"
    if not theorems_dir.is_dir():
        return None  # app-only checkout: nothing to compare against
    tagged_on_disk = 0
    newest_source = 0.0
    for f in theorems_dir.rglob("vs_*.lean"):
        tagged_on_disk += len(_OUTCOME_TAG_RE.findall(f.read_text(encoding="utf-8")))
        newest_source = max(newest_source, f.stat().st_mtime)
    exported = len(json.loads(export_file.read_text(encoding="utf-8"))["theorems"])
    if exported != tagged_on_disk:
        return (
            f"export has {exported} cells but {tagged_on_disk} theorems are tagged "
            f"`@[outcome]` on disk — regenerate it"
        )
    companions_on_disk = sum(
        len(_COMPANION_TAG_RE.findall(f.read_text(encoding="utf-8")))
        for f in theorems_dir.rglob("vs_*.lean")
    )
    exported_companions = len(
        json.loads(export_file.read_text(encoding="utf-8")).get("companions", [])
    )
    if exported_companions != companions_on_disk:
        return (
            f"export has {exported_companions} staggered companions but "
            f"{companions_on_disk} theorems are tagged `@[outcome_companion]` on disk — "
            "regenerate it"
        )
    if newest_source > export_file.stat().st_mtime:
        return "a theorem file is newer than the export — regenerate it to be sure"
    # The tau rows travel with the same exporter, so they are checked here too.
    if tau_phase_dir.is_dir():
        if not tau_export_file.exists():
            return "tau_rows.json is missing — run `lake exe export_outcomes`"
        tagged_rows = sum(
            len(_TAU_TAG_RE.findall(f.read_text(encoding="utf-8")))
            for f in tau_phase_dir.rglob("Phase.lean")
        )
        exported_rows = len(json.loads(tau_export_file.read_text(encoding="utf-8"))["rows"])
        if exported_rows != tagged_rows:
            return (
                f"tau export has {exported_rows} rows but {tagged_rows} theorems are tagged "
                f"`@[tau_row]` on disk — regenerate it"
            )
    return None


def refresh_export(
    engine_dir: Path | None = None,
    export_file: Path | None = None,
    *,
    source: str | None = None,
) -> str:
    """Regenerate the export from the Lean sources. Returns the exporter's stdout.

    Two steps, both required: `lake exe export_outcomes` reads the BUILT `.olean`s
    (it imports `PrisonersDilemma` at runtime rather than depending on it), so running
    it against stale oleans would silently export the previous library. Building
    `OutcomeCheck` alongside the engine also runs the validator + census, so an
    off-template or untagged theorem fails here instead of vanishing from the matrix.
    Raises `RuntimeError` with the tool output on failure.

    `source="sprime"` runs the `S'` twin in `<workspace>/arith`: `lake build --try-cache
    ArithSOutcomeCheck` (the `@[outcomeA]`/`@[floorA]` validator + the paper-zoo coverage
    census) then `lake exe export_sprime_outcomes <export_file>`. `engine_dir` is the
    package directory for either source (the historical positional argument names the
    engine; pass `source="engine"` explicitly there — the library writer does).
    """
    resolved = resolve_source(source)
    if resolved == "sprime":
        package_dir = engine_dir if engine_dir is not None else _ARITH_DIR
        out = export_file if export_file is not None else _EXPORT_FILES["sprime"]
        commands = (
            ["lake", "build", "--try-cache", "ArithSOutcomeCheck"],
            ["lake", "exe", "export_sprime_outcomes", str(out.resolve())],
        )
    else:
        package_dir = engine_dir if engine_dir is not None else _workspace_root() / "engine"
        out = export_file if export_file is not None else _EXPORT_FILES["engine"]
        commands = (
            ["lake", "build", "PrisonersDilemma", "OutcomeCheck"],
            ["lake", "exe", "export_outcomes", str(out.resolve()),
             str(_TAU_EXPORT_FILE.resolve())],
        )
    engine_dir = package_dir
    for cmd in commands:
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
    export_file: Path | None = None,
    *,
    source: str | None = None,
    floor_policy: str | None = None,
) -> list[OutcomeTheorem]:
    """Every accepted `(llm_)outcome_X_vs_Y` theorem with its result.

    Read entirely from the Lean-side export: the shape, the fuel mode, the side conditions
    and the staggering are recovered from ELABORATED TYPES, not guessed from source text.
    The regex extractor this replaced inferred the dagger from "does a binder name start
    with `h`", which silently mis-classified at least one cell.

    `source` picks the system (`settings.CELL_SOURCE`, i.e. `S'` unless `PD_CELL_SOURCE`
    says otherwise); `floor_policy` decides whether `S'` floors join the list
    (`engine_side`, default) or are holes (`restrict_zoo`). An explicit `export_file`
    wins over `source` (the document's own `system` field then decides how it is read).
    A MISSING `S'` export is an error — an empty `S'` matrix would silently read as
    "nothing proven"; the engine file keeps its historical `[]`.

    `theorems_dir` is accepted and IGNORED. It survives because callers pair this with
    `library_bots(theorems_dir)`, which genuinely does read the directory listing; taking
    the argument keeps those call sites symmetric.
    """
    del theorems_dir  # the export, not the source tree, is the authority
    if export_file is None:
        resolved = resolve_source(source)
        export_file = _EXPORT_FILES[resolved]
        if resolved == "sprime" and not export_file.exists():
            raise FileNotFoundError(
                f"the S' export {export_file} does not exist — run `lake exe "
                "export_sprime_outcomes` in arith/ (or `python -m pd_runner.eval."
                "outcome_matrix --refresh`), point PD_SPRIME_EXPORT at a document, or "
                "select the engine's matrix with PD_CELL_SOURCE=engine / source=\"engine\""
            )
    return sorted(_theorems_from_export(export_file, floor_policy), key=lambda t: t.name)


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
    # The status file curates the ENGINE library's open cells (`Open Problem`/`Tried`
    # are about `S` proofs that do not exist yet), so it is pruned against the engine
    # export whatever the configured default source.
    proven = {
        tuple(sorted((t.left_bot, t.right_bot)))
        for t in scan_outcome_theorems(theorems_dir, source="engine")
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


def oriented_pair(t: OutcomeTheorem, row_bot: str) -> tuple[str, str] | None:
    """`t.pair` read from `row_bot`'s side (swapped when `t` is stated from the other)."""
    if t.pair is None:
        return None
    return t.pair if t.left_bot == row_bot else (t.pair[1], t.pair[0])


def engine_flips(
    theorems: list[OutcomeTheorem],
    source: str | None = None,
) -> dict[tuple[str, str], OutcomeTheorem]:
    """For an `S'` cell list: the ENGINE theorem of every pair whose engine value differs
    (either orientation), keyed by the `S'` theorem's ORDERED pair — the `≠` mark.

    Empty for the engine source (nothing to compare against) and when the engine export
    is absent (no flip marks, no crash): the comparison is advisory, the `S'` cells stand
    on their own.
    """
    if resolve_source(source) != "sprime":
        return {}
    engine_file = _EXPORT_FILES["engine"]
    if not engine_file.exists():
        return {}
    engine = index_by_ordered_pair(_theorems_from_export(engine_file))
    flips: dict[tuple[str, str], OutcomeTheorem] = {}
    for t in theorems:
        if t.is_floor:
            # A floor is never a flip: engine-side it IS the engine's value, and
            # hinge-side it differs by construction (the `‡` mark says which).
            continue
        e = engine.get((t.left_bot, t.right_bot)) or engine.get((t.right_bot, t.left_bot))
        if e is None:
            continue
        if oriented_pair(e, t.left_bot) != t.pair:
            flips[(t.left_bot, t.right_bot)] = e
    return flips


def build_outcome_matrix(
    theorems_dir: Path = _THEOREMS_DIR,
    status_file: Path | None = _STATUS_FILE,
    annotate: bool = False,
    *,
    source: str | None = None,
    floor_policy: str | None = None,
) -> tuple[list[str], dict[tuple[str, str], str]]:
    """Upper-triangular matrix of proven outcomes.

    Returns (bot order, cells) where cells maps (row_bot, col_bot) with
    row index ≤ column index to a rendered value. A cell reads from the row
    bot's perspective: (row's action, column's action). When only the
    reversed theorem exists, its pair is swapped to fit.

    `source`/`floor_policy` select the system (see the module doc). Under `S'` a
    floor cell carries `‡` and a cell whose value contradicts the engine's carries `≠`
    (computed against the engine export when present). The curated statuses of
    `outcome_status.toml` describe the ENGINE library's open cells and are rendered
    only for the engine source — an `S'` cell with no statement is simply empty.
    """
    resolved = resolve_source(source)
    theorems = scan_outcome_theorems(theorems_dir, source=resolved, floor_policy=floor_policy)
    bots = library_bots(theorems_dir)
    statuses = (load_status(status_file, bots)
                if status_file is not None and resolved == "engine" else {})
    flips = engine_flips(theorems, resolved)

    by_pair = index_by_ordered_pair(theorems)

    def render(t: OutcomeTheorem, swapped: bool) -> str:
        if t.pair is None:
            return "None"
        row_bot = t.right_bot if swapped else t.left_bot
        a, b = (t.pair[1], t.pair[0]) if swapped else t.pair
        cell = f"({a}, {b})"
        if t.staggered:
            cell += " †"
        if t.is_floor:
            cell += " ‡"
        if (t.left_bot, t.right_bot) in flips:
            cell += " ≠"
        if t.budget_sensitive:
            # Show the (first) companion that disagrees, read from the row bot's side.
            for c in t.companions:
                cp = c.oriented_pair(row_bot)
                if cp != (a, b) and cp is not None:
                    cell += f" ⇄ ({cp[0]}, {cp[1]})"
                    break
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


# The legend, shared by the CLI, the web UI (`GET /matrix` returns it) and the Google
# Sheet push, so the three never drift.
MATRIX_LEGEND: tuple[tuple[str, str], ...] = (
    ("(C, D)", "proven outcome (row bot's action, column bot's action) at ONE shared "
               "budget, a kernel-checked theorem (`@[outcome]` in the engine's S, "
               "`@[outcomeA]` in PA-S')"),
    ("(D, D) ⇄ (C, C)", "BUDGET-SENSITIVE: the shared-budget outcome, then what the pair "
                        "does once one bot is granted a bigger budget (a `…_staggered` "
                        "`@[outcome_companion]` theorem) — both proven"),
    ("†", "STAGGERED ONLY: no shared-budget theorem exists; the cell is proven with one "
          "bot at a bigger budget (LegibleBot/OptimBot two-tier cells)"),
    ("‡", "FLOOR DICHOTOMY (S' only): the engine-side value under FloorPolicy.engine_side; "
          "the cell hinges on bounded consistency of TAct at k — S' proves the hypothesis-"
          "free dichotomy `dich_<L>_vs_<R>` (¬A_k → this value, A_k → the other), not one "
          "value; under `restrict_zoo` the cell is a hole"),
    ("≠", "FLIPS THE ENGINE (S' only): PA-S' proves a value that contradicts the engine's "
          "`@[outcome]` cell for the pair (the engine's value is in the cell note)"),
    ("None", "provably no outcome (the match diverges, e.g. MirrorBot self-play)"),
    ("Open Problem / Tried / Need rework", "curated in app/outcome_status.toml, not a "
                                          "theorem (engine source only)"),
    ("k≫", "(--annotate only) holds at every sufficiently large budget"),
)


_PROVENANCE_LABEL = {
    "engine": "engine S (`@[outcome]`)",
    "sprime": "PA-S' (`@[outcomeA]`)",
    "floor_dichotomy": "PA-S' floor dichotomy (`@[floorA]`)",
}


def cell_note(t: OutcomeTheorem, row_bot: str, engine_flip: OutcomeTheorem | None = None) -> str:
    """A human-readable explanation of one cell, read from `row_bot`'s side — the
    tooltip in the web UI and the cell note in the Google Sheet.

    Everything leads with the ROW-side reading (matching the visible cell text). When
    the library's theorem is stated from the OTHER side, its name goes on its own line
    with its OWN pair — attributing the re-oriented pair to the theorem's name read as
    a contradiction against the Lean statement (`outcome_JustBot_vs_CupodTrollBot`
    proves (D, C); the (CupodTrollBot, JustBot) cell displays it as (C, D)).

    `S'` cells add their provenance; a floor adds its hinge (truncated) and dichotomy;
    `engine_flip` (the engine theorem for the pair, when it disagrees) adds the `≠` line
    with the engine's value read from the row bot's side."""
    swapped = t.left_bot != row_bot
    col_bot = t.left_bot if swapped else t.right_bot
    lines: list[str] = []
    if t.pair is None:
        lines.append(f"{t.name}: provably no outcome ({row_bot} vs {col_bot} diverges).")
    else:
        a, b = (t.pair[1], t.pair[0]) if swapped else t.pair
        left_text, right_text = (t.right_text, t.left_text) if swapped else (t.left_text, t.right_text)
        regime = {"nobudget": "no budget parameter", "universal": "every budget k",
                  "eventual": "every sufficiently large budget k"}.get(t.budget_regime, t.budget_regime)
        where = (f"{left_text} vs {right_text}" if t.staggered
                 else f"{row_bot} vs {col_bot} at one shared budget")
        if swapped:
            lines.append(f"({a}, {b}) read from {row_bot}'s side — {where}; holds at {regime}.")
            lines.append(
                f"Theorem: {t.name}, stated from {t.left_bot}'s side as "
                f"({t.pair[0]}, {t.pair[1]})."
            )
        else:
            lines.append(f"{t.name}: ({a}, {b}) — {where}; holds at {regime}.")
        if t.staggered:
            lines.append("† staggered only: no shared-budget theorem exists for this pair.")
    if t.provenance != "engine":
        lines.append(f"Provenance: {_PROVENANCE_LABEL.get(t.provenance, t.provenance)}.")
    if t.is_floor:
        hinge = t.hinge if len(t.hinge) <= 120 else t.hinge[:117] + "…"
        branch = ("this is the A_k branch (every floor guard provable within budget — "
                  "FloorPolicy.hinge_side, the robustness check); ¬A_k → the engine's value"
                  if t.floor_branch == "hinge_side" else
                  "this is the ¬A_k branch (the engine's value); A_k → the other value")
        lines.append(
            f"‡ floor dichotomy {t.dichotomy or '(unnamed)'}: {branch}. "
            f"Hinge A_k = {hinge or '(not exported)'} "
            "— bounded consistency of TAct at k, open both ways (Pudlák)."
        )
    if engine_flip is not None:
        ep = oriented_pair(engine_flip, row_bot)
        ep_text = "None" if ep is None else f"({ep[0]}, {ep[1]})"
        lines.append(
            f"≠ flips the engine: {engine_flip.name} proves {ep_text} in S "
            f"(read from {row_bot}'s side)."
        )
    for c in t.companions:
        cp = c.oriented_pair(row_bot)
        if cp is None:
            continue
        c_swapped = c.left_bot != row_bot
        cl, cr = (c.right, c.left) if c_swapped else (c.left, c.right)
        verdict = "DIFFERENT outcome" if cp != ((t.pair[1], t.pair[0]) if swapped else t.pair) else "same outcome"
        stated = (f"; the theorem states ({c.pair[0]}, {c.pair[1]}) from {c.left_bot}'s side"
                  if c_swapped and cp != c.pair else "")
        lines.append(
            f"⇄ {c.name}: ({cp[0]}, {cp[1]}) with a budget stagger — {cl} vs {cr} ({verdict}){stated}."
        )
    return "\n".join(lines)


def build_outcome_details(
    theorems_dir: Path = _THEOREMS_DIR,
    *,
    source: str | None = None,
    floor_policy: str | None = None,
) -> dict[tuple[str, str], dict]:
    """Per proven cell (upper triangle, keyed like `build_outcome_matrix`'s cells):
    the theorem, its flags, its companions oriented to the row bot, its provenance
    (`floor`/`hinge`/`dichotomy` for `S'` floors, `flips_engine` with the engine's
    row-side value for a `≠` cell) and the note."""
    resolved = resolve_source(source)
    theorems = scan_outcome_theorems(theorems_dir, source=resolved, floor_policy=floor_policy)
    bots = library_bots(theorems_dir)
    by_pair = index_by_ordered_pair(theorems)
    flips = engine_flips(theorems, resolved)
    order = _bot_order(bots)
    out: dict[tuple[str, str], dict] = {}
    for i, row in enumerate(order):
        for col in order[i:]:
            t = by_pair.get((row, col)) or by_pair.get((col, row))
            if t is None:
                continue
            flip = flips.get((t.left_bot, t.right_bot))
            out[(row, col)] = {
                "theorem": t.name,
                "staggered": t.staggered,
                "budget_sensitive": t.budget_sensitive,
                "companions": [
                    {"name": c.name, "pair": c.oriented_pair(row), "left": c.left, "right": c.right}
                    for c in t.companions
                ],
                "provenance": t.provenance,
                "floor": t.is_floor,
                "hinge": t.hinge,
                "dichotomy": t.dichotomy,
                "flips_engine": (
                    None if flip is None
                    else {"theorem": flip.name, "pair": oriented_pair(flip, row)}
                ),
                "note": cell_note(t, row, flip),
            }
    return out


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


# ---------------------------------------------------------------------------
# Engine vs S' — the source diff (`python -m pd_runner.eval.source_diff`)
# ---------------------------------------------------------------------------

# The 12 base bots of the paper zoos (`SPRIME_SOURCE_OF_TRUTH.md` §0.4): the roster
# `#check_sprime_coverage` demands be a cell or a floor in `S'`.
PAPER_BASE_BOTS: tuple[str, ...] = (
    "CIMCIC", "CooperateBot", "CupodBot", "CupodTrollBot", "DBot", "DIMCID",
    "DefectBot", "DupocBot", "EBot", "OBot", "PrudentBot", "TitForTatBot",
)


@dataclass(frozen=True)
class PairDiff:
    """One unordered pair, both systems read from `left`'s side."""

    left: str
    right: str
    # agree | flip | floor | missing_engine | missing_sprime | missing_both
    kind: str
    engine_pair: tuple[str, str] | None = None
    sprime_pair: tuple[str, str] | None = None
    engine_theorem: str = ""
    sprime_theorem: str = ""
    hinge: str = ""
    dichotomy: str = ""

    @staticmethod
    def fmt(pair: tuple[str, str] | None, present: bool) -> str:
        if not present:
            return "—"
        return "none" if pair is None else f"({pair[0]}, {pair[1]})"


@dataclass(frozen=True)
class ZooDiff:
    key: str
    label: str
    bots: tuple[str, ...]
    pairs: tuple[PairDiff, ...]
    # `S'` floor THEOREMS inside the roster (both orientations count: a pair may carry a
    # dichotomy in each — Cupod×Prudent does), as opposed to `floors`, the unordered pairs.
    floor_rows: tuple[str, ...] = ()

    def _kind(self, kind: str) -> tuple[PairDiff, ...]:
        return tuple(p for p in self.pairs if p.kind == kind)

    @property
    def agreeing(self) -> tuple[PairDiff, ...]:
        return self._kind("agree")

    @property
    def flips(self) -> tuple[PairDiff, ...]:
        return self._kind("flip")

    @property
    def floors(self) -> tuple[PairDiff, ...]:
        return self._kind("floor")

    @property
    def missing(self) -> tuple[PairDiff, ...]:
        return tuple(p for p in self.pairs if p.kind.startswith("missing"))


@dataclass(frozen=True)
class SourceDiff:
    zoos: tuple[ZooDiff, ...]
    engine_file: str
    sprime_file: str

    def zoo(self, key: str) -> ZooDiff:
        for z in self.zoos:
            if z.key == key:
                return z
        raise KeyError(key)

    def render_markdown(self) -> str:
        lines = [
            "# Engine `S` vs PA-`S'` — the cell diff",
            "",
            f"*Generated by `python -m pd_runner.eval.source_diff` from `{self.engine_file}` "
            f"(engine) and `{self.sprime_file}` (S'). Every pair is read from the left bot's "
            "side. A FLIP is a pair both systems state with different values; a FLOOR is a "
            "pair `S'` carries only as a hypothesis-free dichotomy (its listed value is the "
            "engine side, `¬A_k`); MISSING is a pair one side has no statement for.*",
            "",
            "| zoo | bots | pairs | agree | flip | floor (rows) | missing |",
            "|---|---|---|---|---|---|---|",
        ]
        for z in self.zoos:
            lines.append(
                f"| {z.key} | {len(z.bots)} | {len(z.pairs)} | {len(z.agreeing)} | "
                f"{len(z.flips)} | {len(z.floors)} ({len(z.floor_rows)}) | {len(z.missing)} |")
        for z in self.zoos:
            lines += ["", f"## {z.label}", "", f"Bots: {', '.join(z.bots)}", ""]
            if z.flips:
                lines += ["### Flips", "", "| pair | engine | S' | theorems |", "|---|---|---|---|"]
                for p in z.flips:
                    lines.append(
                        f"| {p.left} vs {p.right} | {PairDiff.fmt(p.engine_pair, True)} | "
                        f"{PairDiff.fmt(p.sprime_pair, True)} | `{p.engine_theorem}` / "
                        f"`{p.sprime_theorem}` |")
                lines.append("")
            if z.floors:
                lines += ["### Floors (engine-side value, hinge)", "",
                          "| pair | value | dichotomy | hinge |", "|---|---|---|---|"]
                for p in z.floors:
                    lines.append(
                        f"| {p.left} vs {p.right} | {PairDiff.fmt(p.sprime_pair, True)} | "
                        f"`{p.dichotomy}` | `{p.hinge}` |")
                lines.append("")
            if z.missing:
                lines += ["### Missing", "", "| pair | engine | S' |", "|---|---|---|"]
                for p in z.missing:
                    lines.append(
                        f"| {p.left} vs {p.right} | "
                        f"{PairDiff.fmt(p.engine_pair, p.kind != 'missing_engine' and p.kind != 'missing_both')} | "
                        f"{PairDiff.fmt(p.sprime_pair, p.kind != 'missing_sprime' and p.kind != 'missing_both')} |")
                lines.append("")
            lines.append(f"Agreeing pairs: {len(z.agreeing)} of {len(z.pairs)}.")
        return "\n".join(lines) + "\n"


def _diff_roster(
    key: str,
    label: str,
    bots: tuple[str, ...],
    engine: dict[tuple[str, str], OutcomeTheorem],
    sprime: dict[tuple[str, str], OutcomeTheorem],
    sprime_floor_rows: list[OutcomeTheorem],
) -> ZooDiff:
    def lookup(index: dict, a: str, b: str) -> tuple[OutcomeTheorem | None, tuple[str, str] | None]:
        t = index.get((a, b)) or index.get((b, a))
        return t, (oriented_pair(t, a) if t is not None else None)

    pairs: list[PairDiff] = []
    seen: set[frozenset[str]] = set()
    for a in bots:
        for b in bots:
            k = frozenset((a, b))
            if k in seen:
                continue
            seen.add(k)
            left, right = sorted((a, b))
            e, ep = lookup(engine, left, right)
            s, sp = lookup(sprime, left, right)
            if e is None and s is None:
                kind = "missing_both"
            elif e is None:
                kind = "missing_engine"
            elif s is None:
                kind = "missing_sprime"
            elif s.is_floor:
                kind = "floor"
            elif ep == sp:
                kind = "agree"
            else:
                kind = "flip"
            pairs.append(PairDiff(
                left=left, right=right, kind=kind, engine_pair=ep, sprime_pair=sp,
                engine_theorem=e.name if e else "", sprime_theorem=s.name if s else "",
                hinge=s.hinge if s else "", dichotomy=s.dichotomy if s else "",
            ))
    roster = set(bots)
    rows = tuple(sorted(
        f.name for f in sprime_floor_rows if f.left_bot in roster and f.right_bot in roster))
    return ZooDiff(key=key, label=label, bots=bots, pairs=tuple(pairs), floor_rows=rows)


def diff_sources(bots: tuple[str, ...] | None = None) -> SourceDiff:
    """The engine-vs-`S'` report: per zoo (every kernel-faithful `tau.matrix.ZOOS` roster
    — natives read as their base bot — plus the 12 paper base bots), the unordered
    pairs that agree / flip (both values) / are floors (with hinge) / are missing on
    either side. `bots` restricts the report to one custom roster.

    Floors are read with `engine_side` so their engine-side value is listed; the
    classification itself does not depend on the policy.
    """
    engine_file, sprime_file = _EXPORT_FILES["engine"], _EXPORT_FILES["sprime"]
    engine = index_by_ordered_pair(scan_outcome_theorems(source="engine"))
    sprime_all = scan_outcome_theorems(source="sprime", floor_policy="engine_side")
    sprime = index_by_ordered_pair(sprime_all)
    floor_rows = [t for t in sprime_all if t.is_floor]

    rosters: list[tuple[str, str, tuple[str, ...]]] = []
    if bots is not None:
        rosters.append(("custom", f"custom roster ({len(bots)} bots)", tuple(bots)))
    else:
        from pd_runner.tau.matrix import NATIVE_PLAYERS, ZOOS

        for z in ZOOS.values():
            if z.contradicts_the_kernel:
                continue  # a replay zoo is knowingly wrong; nothing to diff
            base = tuple(dict.fromkeys(
                NATIVE_PLAYERS[b].base if b in NATIVE_PLAYERS else b for b in z.bots))
            rosters.append((z.key, z.label, base))
        rosters.append(("paper12", "the 12 paper base bots (S' coverage census roster)",
                        PAPER_BASE_BOTS))
    return SourceDiff(
        zoos=tuple(_diff_roster(k, lbl, b, engine, sprime, floor_rows) for k, lbl, b in rosters),
        engine_file=str(engine_file), sprime_file=str(sprime_file),
    )


def main() -> None:
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    parser = argparse.ArgumentParser(description="Render the proven outcome matrix.")
    parser.add_argument("--source", choices=list(settings.CELL_SOURCES), default=None,
                        help=f"which system's cells (default: {settings.CELL_SOURCE}, "
                             "from PD_CELL_SOURCE)")
    parser.add_argument("--floor-policy", choices=list(settings.FLOOR_POLICIES), default=None,
                        help=f"S' floors: engine-side cells or holes (default: "
                             f"{settings.FLOOR_POLICY}, from PD_FLOOR_POLICY)")
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
    source = resolve_source(args.source)
    floor_policy = resolve_floor_policy(args.floor_policy)
    print(f"cell source: {source}  floor policy: {floor_policy}")

    if args.refresh:
        try:
            print(refresh_export(source=source).strip())
        except RuntimeError as exc:
            raise SystemExit(f"error: {exc}")
    elif (stale := export_staleness(source=source)) is not None:
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
            summary = push_matrix(annotate=args.annotate, source=source,
                                  floor_policy=floor_policy)
        except SheetsPushError as exc:
            raise SystemExit(f"error: {exc}")
        print(f"pushed {summary['bots']}×{summary['bots']} matrix ({summary['source']}) to "
              f"worksheet {summary['worksheet']!r}: {summary['proven']} proven, "
              f"{summary['none']} None, {summary['open']} open, "
              f"{summary['rework']} need rework, {summary['tried']} tried, "
              f"{summary['empty']} empty, {summary['floors']} floors, "
              f"{summary['flips']} flips")
        print(summary["spreadsheet_url"])
        return

    bots, cells = build_outcome_matrix(annotate=args.annotate, source=source,
                                       floor_policy=floor_policy)
    rendered = format_matrix(bots, cells, fmt=args.format)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(rendered)


if __name__ == "__main__":
    main()

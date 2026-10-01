"""Fetch the Def-4 KERNEL bit tables from the Lean library.

Under the refined Def 4 (the source lift, `Research/Notes/TAUBOTS.md`), each tau bot's
entire per-hypothesis content is its BIT TABLE — what each compiled instance plays —
certified in `Tau/Theorems/<Bot>/Phase.lean` as an UNCONDITIONAL `RowSpec` theorem
(`Tau/RowSpec.lean`, tagged `@[tau_row]`):

    @[tau_row] theorem dupocRowSpec : RowSpec .dupoc tauOrder dupocRow

The Lean linter (`Tau/Lint.lean`) validates every tagged row against the roster and
EVALUATES the row function to literal bits; `lake exe export_outcomes` writes them to
`app/generated/tau_rows.json` (digest-protected). This module reads that file, so
`compare.py` verifies the Python side against the KERNEL rather than trusting its own
arithmetic. That check is load-bearing history: the kernel-vs-model discipline caught
five real Python bugs during milestone 1 and the inverted stipulation that triggered the
2026-08-12 audit.

Until 2026-08-27 this module regex-scanned a literal `VoteBits` list out of the source —
and could not see that the scanned theorem was CONDITIONAL on Löb-gated hypotheses
discharged only in the phase theorem. The exported rows are unconditional at large `k`.

**Scope.** A template with no tagged row has no certified bits and `kernel_bits` omits
it — absence is the honest signal that a row is predicted rather than proven (the Lean
census makes that a build failure, so in practice every `Tmpl` has a row).

**Two sources (2026-10-01, Phase 4 of `SPRIME_SOURCE_OF_TRUTH.md`).** Every reader takes
`source` (`settings.CELL_SOURCE` by default, i.e. PA-`S'`): `TAU_EXPORTS` names one row
file per `CellSource`. The `S'` file (`sprime_tau_rows.json`, written by
`lake exe export_sprime_outcomes` from the `@[tau_rowA]`/`@[tau_floor_bitA]` theorems in
`arith/ArithS/Tau/`) is the engine's schema over the 14-template `PAPER_ORDER` plus
`"system": "sprime"` and a `floor_bits` array. It differs from the engine's file in
two ways the readers encode rather than paper over:

* a FLOOR BIT (`FloorBitA`, the engine-side half of the base cell's dichotomy) loads as
  its engine-side action in `kernel_bits`, and `kernel_bit_provenance` says
  `"floor_dichotomy"` for it (`"theorem"` for a `RowSpecA` slot); `kernel_floor_bits`
  carries the hinge text and the `dich_` name;
* a slot in neither a row's `bits` nor `floor_bits` is ABSENT from the table — NOT
  `"N"`. The engine's `_DIVERGENT` fill applies to ONE known slot (τ(Mirror)'s
  diagonal, a proven non-terminating cell); on `S'` an absent slot means "not yet
  stated" (the export is PARTIAL during the Phase-3 rollout: a row lists only its proved
  non-floor slots, and whole templates may be missing), and `tau/matrix.py` reports the
  coverage (`TauMatrix.kernel_coverage`) rather than inventing a value.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path

from pd_runner.settings import resolve_source


def _workspace_root() -> Path:
    """Walk up from this file to the workspace root (the dir containing engine/)."""
    p = Path(__file__).resolve()
    for parent in p.parents:
        if (parent / "engine" / "PrisonersDilemma").is_dir():
            return parent
    raise FileNotFoundError(
        "cannot locate the workspace root (no engine/PrisonersDilemma above "
        f"{p}) — pass an explicit path to kernel_bits"
    )


TAU_EXPORTS: dict[str, str] = {
    "engine": "app/generated/tau_rows.json",
    "sprime": "app/generated/sprime_tau_rows.json",
}
"""One kernel row file per `CellSource` (workspace-relative). The engine's is written by
`lake exe export_outcomes`, the `S'` one by `lake exe export_sprime_outcomes`."""

TAU_EXPORT = TAU_EXPORTS["engine"]
"""The engine's row file (historical name)."""


def _default_tau_export_files() -> dict[str, Path]:
    try:
        root = _workspace_root()
    except FileNotFoundError:
        return {}
    files = {s: root / rel for s, rel in TAU_EXPORTS.items()}
    # `PD_SPRIME_TAU_EXPORT` points the `S'` reader at an alternative document (the
    # test-suite's ledger-derived sample while the real export does not exist yet);
    # it never applies to the engine file — same contract as `PD_SPRIME_EXPORT`.
    override = os.getenv("PD_SPRIME_TAU_EXPORT")
    if override:
        files["sprime"] = Path(override)
    return files


_TAU_EXPORT_FILES: dict[str, Path] = _default_tau_export_files()
"""The resolved row file per source, consulted at CALL time (never captured as a default
argument), so pointing a source elsewhere is one dict assignment (`tests/conftest.py`)."""


def tau_export_file(source: str | None = None) -> Path:
    """The row file a `CellSource` reads (default: `settings.CELL_SOURCE`)."""
    resolved = resolve_source(source)
    try:
        return _TAU_EXPORT_FILES[resolved]
    except KeyError:
        return _workspace_root() / TAU_EXPORTS[resolved]


TAU_ORDER: tuple[str, ...] = (
    "coop", "defect", "tftSim", "tftPf", "dupoc", "ebot", "just", "obot", "guardian",
    "dbot", "cupodTroll", "cupod", "cimcic", "dimcid", "prudent", "maxconfidence",
    "minconfidence", "mirror")
"""The Lean `tauOrder` slot order. The export carries the kernel's own copy and
`kernel_bits` refuses to run if the two disagree."""

PAPER_ORDER: tuple[str, ...] = (
    "coop", "defect", "tftSim", "dupoc", "ebot", "obot", "dbot", "cupodTroll", "cupod",
    "dimcid", "cimcic", "prudent", "maxconfidence", "minconfidence")
"""`ArithS.Tau.paperOrder` (`arith/ArithS/Tau/Spec.lean`): the 14 paper templates — the
columns of the §3 table of `SPRIME_SOURCE_OF_TRUTH.md`. A SUBSET of `TAU_ORDER` (the four
engine-only templates `tftPf just guardian mirror` dropped) but NOT a sub-order of it: the
paper order lists `dimcid` before `cimcic`, the engine's `tauOrder` the other way round.
The `S'` row file's `order` must equal it."""

assert set(PAPER_ORDER) < set(TAU_ORDER), "PAPER_ORDER must be a proper subset of TAU_ORDER"

# A slot the row's order does not cover (τ(Mirror)'s divergent diagonal, stated over
# `tauOrderInit`) is recorded as "N" — the same fifth state the base matrix uses for a
# proven-`none` outcome, so the comparison can say "agrees" there rather than inventing a D.
# ENGINE ONLY: on `S'` an absent slot stays absent (see the module docstring).
_DIVERGENT = "N"

PROVENANCE_THEOREM = "theorem"
PROVENANCE_FLOOR = "floor_dichotomy"
PROVENANCE_DIVERGENT = "divergent"
"""`kernel_bit_provenance` values: a `RowSpec`/`RowSpecA` slot, a `FloorBitA` slot (`S'`
only), or the engine's `_DIVERGENT` fill (τ(Mirror)'s diagonal, engine only)."""


@dataclass(frozen=True)
class FloorBit:
    """One `@[tau_floor_bitA]` theorem: the engine-side action of a floor slot, with the
    hinge `A_k` (pretty text) under whose FAILURE it is forced, and the base cell's
    dichotomy name."""

    template: str
    slot: str
    action: str
    hinge: str
    dichotomy: str


def _verify_tau_digest(data: dict, export: Path) -> None:
    """Reject a hand-edited row file. The engine hashes `rows`; a `S'` document hashes
    `rows ++ floor_bits` (`ArithS/Tau/Export.lean`), each row dumped compactly with sorted
    keys, FNV-1a over the concatenation — the `Outcome/Export.lean` algorithm."""
    from pd_runner.eval.outcome_matrix import _fnv1a64

    claimed = data.get("source_digest")
    if claimed is None:
        raise ValueError(f"{export}: missing `source_digest`")
    hashed = list(data["rows"])
    if data.get("system") == "sprime":
        hashed += list(data.get("floor_bits", []))
    rows = [json.dumps(t, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            for t in hashed]
    actual = str(_fnv1a64("".join(rows)))
    if actual != claimed:
        exporter = ("lake exe export_sprime_outcomes" if data.get("system") == "sprime"
                    else "lake exe export_outcomes")
        raise ValueError(
            f"{export}: source_digest mismatch — the file was edited by hand or is stale "
            f"(claimed {claimed}, recomputed {actual}). Regenerate it with `{exporter}`; "
            "never hand-edit proven rows."
        )


def _load_export(path: Path | None = None, *, source: str | None = None) -> dict:
    """Read and validate one row file.

    `source` picks the document (`settings.CELL_SOURCE` by default). An explicit `path`
    wins; with no `source` its document's own `system` field decides how it is read (as
    `scan_outcome_theorems` does for `export_file`), and with one the document must BE
    that system. The engine schema: the whole `TAU_ORDER`, no `system`. The `S'` schema:
    `"system": "sprime"`, `PAPER_ORDER`, every row slot / floor bit a paper slot, never
    both, templates and slots possibly absent (a partial export).
    """
    if path is not None and source is None:
        export = path
        if not export.exists():
            raise FileNotFoundError(f"{export} not found")
        data = json.loads(export.read_text(encoding="utf-8"))
        resolved = data.get("system", "engine")
        if resolved not in TAU_EXPORTS:
            raise ValueError(f"{export}: unknown system {resolved!r}")
    else:
        resolved = resolve_source(source)
        export = path if path is not None else tau_export_file(resolved)
        if not export.exists():
            exporter = ("`lake exe export_sprime_outcomes` in arith/" if resolved == "sprime"
                        else "`lake exe export_outcomes` (or `uv run python -m "
                             "pd_runner.eval.outcome_matrix --refresh`)")
            raise FileNotFoundError(f"{export} not found — run {exporter}")
        data = json.loads(export.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1:
        raise ValueError(f"{export}: unsupported schema_version {data.get('schema_version')!r}")
    system = data.get("system", "engine")
    if system != resolved:
        raise ValueError(
            f"{export}: a {system!r} row file read as the {resolved!r} source — the two "
            "systems' rows disagree by theorem (the DIMCID cells); point the source at "
            "its own export"
        )
    _verify_tau_digest(data, export)
    order = tuple(data["order"])
    if resolved == "engine":
        if order != TAU_ORDER:
            raise ValueError(
                f"{export}: the kernel's tauOrder {order} differs from TAU_ORDER — update the "
                "constant"
            )
        return data
    if order != PAPER_ORDER:
        raise ValueError(
            f"{export}: the kernel's paperOrder {order} differs from PAPER_ORDER — update "
            "the constant"
        )
    paper = set(PAPER_ORDER)
    seen: dict[str, set[str]] = {}
    for row in data["rows"]:
        tmpl = row["template"]
        if tmpl not in paper:
            raise ValueError(f"{export}: row {tmpl!r} is not a paper template")
        unknown = set(row["bits"]) - paper
        if unknown:
            raise ValueError(f"{export}: row {tmpl}: unknown slots {sorted(unknown)}")
        row_order = row.get("order")
        if isinstance(row_order, list) and set(row_order) - paper:
            raise ValueError(
                f"{export}: row {tmpl}: order names non-paper slots "
                f"{sorted(set(row_order) - paper)}")
        bad = {s: a for s, a in row["bits"].items() if a not in ("C", "D")}
        if bad:
            raise ValueError(f"{export}: row {tmpl}: non-action bits {bad}")
        if tmpl in seen:
            raise ValueError(f"{export}: template {tmpl!r} has two rows")
        seen[tmpl] = set(row["bits"])
    for fb in data.get("floor_bits", []):
        tmpl, slot = fb["template"], fb["slot"]
        if tmpl not in paper or slot not in paper:
            raise ValueError(f"{export}: floor bit ({tmpl}, {slot}) is not a paper cell")
        if fb["action"] not in ("C", "D"):
            raise ValueError(f"{export}: floor bit ({tmpl}, {slot}): action {fb['action']!r}")
        if slot in seen.get(tmpl, set()):
            raise ValueError(
                f"{export}: ({tmpl}, {slot}) is both a row slot and a floor bit — the Lean "
                "census forbids it; the export is inconsistent"
            )
        seen.setdefault(tmpl, set())
        if slot in seen[tmpl]:
            raise ValueError(f"{export}: floor bit ({tmpl}, {slot}) stated twice")
        seen[tmpl].add(slot)
    return data


def _tables(data: dict, source: str) -> tuple[
        dict[str, dict[str, str]], dict[str, dict[str, str]], dict[str, dict[str, FloorBit]]]:
    """(bits, provenance, floor bits) from a validated document."""
    bits: dict[str, dict[str, str]] = {}
    prov: dict[str, dict[str, str]] = {}
    floors: dict[str, dict[str, FloorBit]] = {}
    if source == "engine":
        for row in data["rows"]:
            stated = dict(row["bits"])
            unknown = set(stated) - set(TAU_ORDER)
            if unknown:
                raise ValueError(f"row {row['template']}: unknown slots {sorted(unknown)}")
            bits[row["template"]] = {s: stated.get(s, _DIVERGENT) for s in TAU_ORDER}
            prov[row["template"]] = {
                s: (PROVENANCE_THEOREM if s in stated else PROVENANCE_DIVERGENT)
                for s in TAU_ORDER}
        if not bits:
            raise ValueError("tau_rows.json holds no rows — the export is empty")
        return bits, prov, floors
    for row in data["rows"]:
        tmpl = row["template"]
        bits[tmpl] = {s: row["bits"][s] for s in PAPER_ORDER if s in row["bits"]}
        prov[tmpl] = {s: PROVENANCE_THEOREM for s in bits[tmpl]}
    for fb in data.get("floor_bits", []):
        tmpl, slot = fb["template"], fb["slot"]
        bits.setdefault(tmpl, {})[slot] = fb["action"]
        prov.setdefault(tmpl, {})[slot] = PROVENANCE_FLOOR
        floors.setdefault(tmpl, {})[slot] = FloorBit(
            template=tmpl, slot=slot, action=fb["action"],
            hinge=fb.get("hinge", ""), dichotomy=fb.get("dichotomy", ""))
    # keep paper order inside every row
    bits = {t: {s: r[s] for s in PAPER_ORDER if s in r} for t, r in bits.items()}
    prov = {t: {s: r[s] for s in PAPER_ORDER if s in r} for t, r in prov.items()}
    return bits, prov, floors


def scan_bit_theorems(path: Path | None = None, *, source: str | None = None
                      ) -> dict[str, dict[str, str]]:
    """The kernel rows → `{lean_tmpl: {slot_tmpl: "C"|"D"|"N"}}`.

    Kept under its historical name; it reads the export, not the sources. On the engine
    every stated row is complete over `TAU_ORDER` (`"N"` at the divergent slot); on `S'`
    a row holds exactly the stated slots — theorem bits AND floor bits (at their
    engine-side action) — and a template with nothing stated is absent.
    """
    data = _load_export(path, source=source)
    return _tables(data, data.get("system", "engine"))[0]


def kernel_bits(path: Path | None = None, *, source: str | None = None
                ) -> dict[str, dict[str, str]]:
    """The kernel-certified bit tables, keyed by Lean `Tmpl` constructor names."""
    return scan_bit_theorems(path, source=source)


def kernel_bit_provenance(path: Path | None = None, *, source: str | None = None
                          ) -> dict[str, dict[str, str]]:
    """Parallel to `kernel_bits`: per slot, `"theorem"` (a `RowSpec`/`RowSpecA` slot),
    `"floor_dichotomy"` (a `S'` `FloorBitA` — the value is the engine-side half of a
    dichotomy, not a theorem about the cell) or `"divergent"` (the engine's `"N"` fill)."""
    data = _load_export(path, source=source)
    return _tables(data, data.get("system", "engine"))[1]


def kernel_floor_bits(path: Path | None = None, *, source: str | None = None
                      ) -> dict[str, dict[str, FloorBit]]:
    """The `S'` floor bits with their hinge text, `{tmpl: {slot: FloorBit}}`; `{}` on the
    engine source (its rows have no floors)."""
    data = _load_export(path, source=source)
    return _tables(data, data.get("system", "engine"))[2]


# ── The template name tables ───────────────────────────────────────────────────
#
# Moved here from the deleted `def4.py` (2026-08-24). They are pure naming
# tables — which templates exist, which base bot each one lifts, and which Lean
# `Tmpl` constructor names it — with no model arithmetic attached, so they
# belong with the kernel-scanning layer that the certification now rests on.

TEMPLATES: tuple[str, ...] = (
    "TauCooperate",
    "TauDefect",
    "TauTFTSim",
    "TauTFTPf",
    "TauDupoc",
    "TauEBot",
    "TauJust",
    "TauOBot",
    "TauGuardian",
    "TauDBot",
    "TauCupodTroll",
    "TauCupod",
    "TauCIMCIC",
    "TauDIMCID",
    "TauPrudent",
    "TauMaxConfidence",
    "TauMinConfidence",
    "TauMirror",
)
"""Canonical template order."""

BASE_OF: dict[str, str] = {
    "TauCooperate": "CooperateBot",
    "TauDefect": "DefectBot",
    "TauTFTSim": "TitForTatBot",
    "TauDupoc": "DupocBot",
    "TauEBot": "EBot",
    "TauJust": "JustBot",
    "TauOBot": "OBot",
    "TauGuardian": "GuardianBot",
    "TauDBot": "DBot",
    "TauCupodTroll": "CupodTrollBot",
    "TauCupod": "CupodBot",
    "TauCIMCIC": "CIMCIC",
    "TauDIMCID": "DIMCID",
    "TauPrudent": "PrudentBot",
    "TauMaxConfidence": "DupocBot",
    "TauMinConfidence": "DupocBot",
    "TauMirror": "MirrorBot",
}
"""Which base bot each template lifts. `TauTFTPf` has NO entry: it is the PROVER
reading of TitForTatBot's question, a tau-only variant with no base bot, so the
certification compares it nowhere (2026-08-25). `TauTFTSim` is the lift of
TitForTatBot.

`TauMaxConfidence` (2026-08-27) is NOT a lift — it is the first NATIVE player, the
MAX aggregator over Dupoc's test (`Tau/Bots/TauMaxConfidence.lean`) — but in the
HYPOTHESIS role it IS Dupoc: `inst` depends only on specs and its spec is Dupoc's,
so its kernel row equals `dupocRow` and every other row's `.maxconfidence` bit equals
its `.dupoc` bit (`maxconfidenceRow_eq_dupocRow`, the `rfl` bridges in `Zoo.lean`).
Mapping it to `DupocBot` makes the certification check exactly that against the
base matrix — the kernel-backed form of the matrix CLONE the Python zoo uses
(`matrix.NATIVE_PLAYERS`). The aggregator is a player fact, not a row fact, and
lives in `play.py`.

`TauMinConfidence` (2026-09-01) is the second native player — the MIN / worst-case
aggregator over the same test — and maps to `DupocBot` for exactly the same
reason: its kernel row equals `dupocRow` (`minconfidenceRow_eq_dupocRow`, the
`inst_minconfidence_*` bridges), and its entangled pairs compile to the very same
`.sys` system as MaxConfidenceBot's, so no new Löb content exists at the row level."""

LEAN_SLOT: dict[str, str] = {
    "TauCooperate": "coop",
    "TauDefect": "defect",
    "TauTFTSim": "tftSim",
    "TauTFTPf": "tftPf",
    "TauDupoc": "dupoc",
    "TauEBot": "ebot",
    "TauJust": "just",
    "TauOBot": "obot",
    "TauGuardian": "guardian",
    "TauDBot": "dbot",
    "TauCupodTroll": "cupodTroll",
    "TauCupod": "cupod",
    "TauCIMCIC": "cimcic",
    "TauDIMCID": "dimcid",
    "TauPrudent": "prudent",
    "TauMaxConfidence": "maxconfidence",
    "TauMinConfidence": "minconfidence",
    "TauMirror": "mirror",
}
"""Template name → the Lean `Tmpl` constructor, for reading the bit tables."""

TEMPLATE_OF_BOT: dict[str, str] = {
    "CooperateBot": "TauCooperate",
    "DefectBot": "TauDefect",
    "TitForTatBot": "TauTFTSim",
    "DupocBot": "TauDupoc",
    "EBot": "TauEBot",
    "JustBot": "TauJust",
    "OBot": "TauOBot",
    "GuardianBot": "TauGuardian",
    "DBot": "TauDBot",
    "CupodTrollBot": "TauCupodTroll",
    "CupodBot": "TauCupod",
    "CIMCIC": "TauCIMCIC",
    "DIMCID": "TauDIMCID",
    "PrudentBot": "TauPrudent",
    "MirrorBot": "TauMirror",
    "MaxConfidenceBot": "TauMaxConfidence",
    "MinConfidenceBot": "TauMinConfidence",
}
"""Zoo bot → the template that carries ITS OWN kernel row (2026-09-01, the Def-4
substrate). NOT the inverse of `BASE_OF`: the natives map to their own templates
here (their rows are theirs, even though the VALUES are Dupoc's), whereas `BASE_OF`
maps their templates to `DupocBot` because that is what the certification compares
them against. `TauTFTPf` appears in neither: it is the prover reading of TFT's
question, no bot's own row."""

PAPER_TEMPLATES: tuple[str, ...] = tuple(
    next(t for t, s in LEAN_SLOT.items() if s == slot) for slot in PAPER_ORDER)
"""The 14 paper templates (`PAPER_ORDER`) by template name, in paper order — the scope
of the `S'` certification (`compare.direct_kernel_vs_base` on `source="sprime"`)."""


@dataclass(frozen=True)
class RecordedDivergence:
    """One bit at which the `S'` kernel row and the `S'` base cell DISAGREE by theorem
    (`SPRIME_SOURCE_OF_TRUTH.md` §3, the 2026-10-01 FINDING): `kind` is `"value"` (the
    stated bit differs from the base cell's action) or `"provenance"` (same value, but a
    `FloorBitA` on a base cell that is a theorem)."""

    kind: str
    reason: str


_RED_CELL = ("the tau image of the red cell: outcome_DupocBot_vs_CupodBot is a theorem in "
             "the base by τ-symmetry, but inside one compiled .sys system the two members' "
             "guards are not τ-images, so the bit is a FLOOR in S' (Tau/Entangled/DupocCupod.lean)")

SPRIME_RECORDED_DIVERGENCES: dict[tuple[str, str], RecordedDivergence] = {
    ("dupoc", "cupod"): RecordedDivergence("provenance", _RED_CELL),
    ("maxconfidence", "cupod"): RecordedDivergence("provenance", _RED_CELL),
    ("minconfidence", "cupod"): RecordedDivergence("provenance", _RED_CELL),
    ("cupod", "dupoc"): RecordedDivergence("provenance", _RED_CELL),
    ("cupod", "maxconfidence"): RecordedDivergence("provenance", _RED_CELL),
    ("cupod", "minconfidence"): RecordedDivergence("provenance", _RED_CELL),
}
"""The six `S'` bits at which the kernel row and the base cell differ BY THEOREM — keyed by
Lean `Tmpl` slot names `(template, hypothesis)`, machine-checked in
`arith/ArithS/Tau/Rows/*`: the six PROVENANCE divergences (floor bits on the tau images of
the red cell, a base theorem; independent of the coding). The matrix loader
(`matrix._kernel_rows_for`) does not raise on these and does NOT consult them (the base
cell is played, so every downstream number is unchanged); the certification
(`compare.direct_kernel_vs_base`) reports them as whitelisted divergences. Anything else
that disagrees is still a bug by definition. Engine source: never consulted.

History (2026-10-01). Phases 3b–3d recorded twelve: these six and six VALUE divergences
(`cimcic × tftSim`, `dimcid × {tftSim, ebot, obot, dbot, cupodTroll}`), artefacts of the
pre-abstraction coding (the budget-snapshot obstruction, `Tau/NeverFits.lean`). Route (c)
made generic (Phase 2c) dissolved them and Phase 3e re-proved five with the table's
values; the six VALUE entries are REMOVED. The sixth, `dimcid × ebot`, is not a recorded
divergence either: its row slot is UNSTATED in Lean (`Tau/NeverFitsSys.dimcid_ebot_C` —
budget abstraction does not descend into the closed system τ(EBot)'s third watch freezes,
so under the present coding the compiled bit is C, the engine's value, against the base
cell's D), hence UNCOVERED here and played from the `S'` base cell like any unstated bit.

An entry is a claim that the Lean export DISAGREES with the base cell in exactly the
recorded way. An entry that no longer fires — the bit is stated, the cell is proven, and
they AGREE in value and provenance — is STALE (Lean moved; delete the entry): the loader
issues a `StaleDivergenceWarning` naming it, rather than carrying a dead whitelist line."""


class StaleDivergenceWarning(UserWarning):
    """A recorded `S'` divergence (`SPRIME_RECORDED_DIVERGENCES`) did not fire at load: the
    kernel row states the bit and it AGREES with the proven base cell (value and
    provenance). Either the entry is stale (remove it) or the row file is not the real
    export (the cell-derived test sample states no divergence by construction)."""


def recorded_divergence(source: str, template_slot: str | None, hypothesis_slot: str | None
                        ) -> RecordedDivergence | None:
    """The recorded divergence at a Lean-slot-keyed bit on `source`, else `None`."""
    if source != "sprime" or template_slot is None or hypothesis_slot is None:
        return None
    return SPRIME_RECORDED_DIVERGENCES.get((template_slot, hypothesis_slot))


def _per_bot(tables: dict[str, dict[str, str]]) -> dict[str, dict[str, str]]:
    slot_of_bot = {b: LEAN_SLOT[t] for b, t in TEMPLATE_OF_BOT.items()}
    out: dict[str, dict[str, str]] = {}
    for bot, tmpl in TEMPLATE_OF_BOT.items():
        row = tables.get(LEAN_SLOT[tmpl])
        if row is None:
            continue
        out[bot] = {hb: row[slot] for hb, slot in slot_of_bot.items() if slot in row}
    return out


def kernel_row_bits(path: Path | None = None, *, source: str | None = None
                    ) -> dict[str, dict[str, str]]:
    """Per-BOT kernel test bits: actor bot → hypothesis bot → `"C"`/`"D"`/`"N"`.

    The Def-4 substrate the tau matrix plays from (2026-09-01): each covered bot's
    per-hypothesis test bits come from its own kernel-proven `RowSpec` row
    (`tau_rows.json`, or `sprime_tau_rows.json` on `source="sprime"`), keyed by bot
    names on both axes via `TEMPLATE_OF_BOT` + `LEAN_SLOT`. A bot with no template
    (WaryBot, LegibleBot, …) — or, on `S'`, no row stated yet — simply has no entry,
    and a `S'` row may be PARTIAL (only its stated slots); `load_tau_matrix` falls back
    to the base cells there and records the matrix's kernel coverage. A native player
    (`MaxConfidenceBot`, `MinConfidenceBot`) reads ITS OWN template's row.
    """
    return _per_bot(kernel_bits(path, source=source))


def kernel_row_provenance(path: Path | None = None, *, source: str | None = None
                          ) -> dict[str, dict[str, str]]:
    """`kernel_row_bits`' provenance twin: actor bot → hypothesis bot →
    `"theorem"` | `"floor_dichotomy"` | `"divergent"` (`kernel_bit_provenance`)."""
    return _per_bot(kernel_bit_provenance(path, source=source))


# ── The comparison zoos (base-bot keyed, as the σ channels are) ────────────────

CONTROL_ZOO: dict[str, str] = {
    "DupocBot": "TauDupoc",
    "CooperateBot": "TauCooperate",
    "DefectBot": "TauDefect",
    "TitForTatBot": "TauTFTSim",
}
"""base bot → the template that lifts it. Base TFT maps to the BEHAVIORAL
variant (that is what base TitForTatBot is); the prover variant appears in the
bit tables as the budget-gap twin."""

CONTROL_BOTS: tuple[str, ...] = (
    "DupocBot",
    "CooperateBot",
    "DefectBot",
    "TitForTatBot",
)

SEPARATING_ZOO: dict[str, str] = {**CONTROL_ZOO, "EBot": "TauEBot"}
"""Control + EBot."""

SEPARATING_BOTS: tuple[str, ...] = CONTROL_BOTS + ("EBot",)


def main() -> None:
    import argparse

    from pd_runner import settings

    parser = argparse.ArgumentParser(description="Print the kernel tau bit tables.")
    parser.add_argument("--source", choices=list(settings.CELL_SOURCES), default=None,
                        help=f"row file (default: {settings.CELL_SOURCE})")
    args = parser.parse_args()
    source = resolve_source(args.source)
    tables = kernel_bits(source=source)
    prov = kernel_bit_provenance(source=source)
    order = TAU_ORDER if source == "engine" else PAPER_ORDER
    print(f"kernel bit tables ({tau_export_file(source)}, slot order = "
          f"{'tauOrder' if source == 'engine' else 'paperOrder'}; ‡ = floor bit, "
          "· = not stated):")
    for tmpl in order:
        row = tables.get(tmpl)
        if row is None:
            print(f"  {tmpl:14s}  (no certified row)")
            continue
        cells = []
        for s in order:
            if s not in row:
                cells.append(" ·")
            else:
                cells.append(row[s] + ("‡" if prov[tmpl][s] == PROVENANCE_FLOOR else " "))
        print(f"  {tmpl:14s}  " + " ".join(cells))


if __name__ == "__main__":
    main()

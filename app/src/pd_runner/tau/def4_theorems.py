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
"""

from __future__ import annotations

import json
from pathlib import Path


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


TAU_EXPORT = "app/generated/tau_rows.json"

TAU_ORDER: tuple[str, ...] = (
    "coop", "defect", "tftSim", "tftPf", "dupoc", "ebot", "just", "obot", "guardian",
    "dbot", "cupodTroll", "cupod", "cimcic", "dimcid", "prudent", "mirror")
"""The Lean `tauOrder` slot order. The export carries the kernel's own copy and
`kernel_bits` refuses to run if the two disagree."""

# A slot the row's order does not cover (τ(Mirror)'s divergent diagonal, stated over
# `tauOrderInit`) is recorded as "N" — the same fifth state the base matrix uses for a
# proven-`none` outcome, so the comparison can say "agrees" there rather than inventing a D.
_DIVERGENT = "N"


def _load_export(path: Path | None = None) -> dict:
    export = path if path is not None else _workspace_root() / TAU_EXPORT
    if not export.exists():
        raise FileNotFoundError(
            f"{export} not found — run `lake exe export_outcomes` (or "
            "`uv run python -m pd_runner.eval.outcome_matrix --refresh`)"
        )
    data = json.loads(export.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1:
        raise ValueError(f"{export}: unsupported schema_version {data.get('schema_version')!r}")
    from pd_runner.eval.outcome_matrix import _verify_digest

    _verify_digest(data, export, key="rows")
    order = tuple(data["order"])
    if order != TAU_ORDER:
        raise ValueError(
            f"{export}: the kernel's tauOrder {order} differs from TAU_ORDER — update the "
            "constant"
        )
    return data


def scan_bit_theorems(path: Path | None = None) -> dict[str, dict[str, str]]:
    """The kernel rows → `{lean_tmpl: {slot_tmpl: "C"|"D"|"N"}}`.

    Kept under its historical name; it reads the export, not the sources.
    """
    data = _load_export(path)
    tables: dict[str, dict[str, str]] = {}
    for row in data["rows"]:
        bits = dict(row["bits"])
        unknown = set(bits) - set(TAU_ORDER)
        if unknown:
            raise ValueError(f"row {row['template']}: unknown slots {sorted(unknown)}")
        tables[row["template"]] = {s: bits.get(s, _DIVERGENT) for s in TAU_ORDER}
    if not tables:
        raise ValueError("tau_rows.json holds no rows — the export is empty")
    return tables


def kernel_bits(path: Path | None = None) -> dict[str, dict[str, str]]:
    """The kernel-certified bit tables, keyed by Lean `Tmpl` constructor names."""
    return scan_bit_theorems(path)


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
    "TauMirror": "MirrorBot",
}
"""Which base bot each template lifts. `TauTFTPf` has NO entry: it is the PROVER
reading of TitForTatBot's question, a tau-only variant with no base bot, so the
certification compares it nowhere (2026-08-25). `TauTFTSim` is the lift of
TitForTatBot."""

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
    "TauMirror": "mirror",
}
"""Template name → the Lean `Tmpl` constructor, for reading the bit tables."""


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
    tables = kernel_bits()
    print("kernel bit tables (app/generated/tau_rows.json, slot order = tauOrder):")
    for tmpl in TAU_ORDER:
        row = tables.get(tmpl)
        if row is None:
            print(f"  {tmpl:8s}  (no certified row)")
        else:
            print(f"  {tmpl:8s}  " + " ".join(row[s] for s in TAU_ORDER))


if __name__ == "__main__":
    main()

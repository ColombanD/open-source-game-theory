"""Fetch the Def-4 KERNEL bit tables from the Lean library.

Under the refined Def 4 (the source lift, `DEF4_TVOTE_ROADMAP.md`), each tau bot's
entire per-hypothesis content is its BIT TABLE — what each compiled instance plays —
certified in `Tau/Theorems/<Bot>/Phase.lean` as a `VoteBits` theorem per template:

    theorem eBits ... :
        VoteBits (vecOf (tauZoo k) .ebot w tauOrder)
          [(w .coop, .D), (w .defect, .D), (w .tftSim, .C),
           (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] := ...

This module scans those theorems (purely static — no Lean invocation; the kernel
already checked every statement) and exposes them as per-template action rows, so
`compare.py` can verify the Python spec-mirror (`def4.decide`) against the KERNEL
rather than trusting its own arithmetic. That check is load-bearing history: the
kernel-vs-model discipline caught five real Python bugs during milestone 1 and the
inverted stipulation that triggered the 2026-08-12 audit.

**Scope.** Only the six-template `tauZoo` has bit theorems. A template modelled in
Python but absent here has NO certified row, and `kernel_bits` omits it — absence is
the honest signal that a row is predicted rather than proven.
"""

from __future__ import annotations

import re
from pathlib import Path


def _workspace_root() -> Path:
    """Walk up from this file to the workspace root (the dir containing engine/)."""
    p = Path(__file__).resolve()
    for parent in p.parents:
        if (parent / "engine" / "PrisonersDilemma").is_dir():
            return parent
    raise FileNotFoundError(
        "cannot locate the workspace root (no engine/PrisonersDilemma above "
        f"{p}) — pass an explicit path to scan_bit_theorems"
    )


PHASE_GLOB = "engine/PrisonersDilemma/Tau/Theorems/*/Phase.lean"

TAU_ORDER: tuple[str, ...] = (
    "coop", "defect", "tftSim", "tftPf", "dupoc", "ebot", "just", "obot", "guardian",
    "dbot", "cupodTroll", "cupod", "cimcic", "dimcid")
"""The Lean `tauOrder` slot order — every bit list is stated in this order."""

_BITS_RE = re.compile(
    r"theorem\s+(\w+)\s.*?VoteBits\s*\(vecOf\s*\(tauZoo\s+k\)\s*\.(\w+)\s+w\s+tauOrder\)\s*"
    r"\[(.*?)\]",
    re.S,
)
_ENTRY_RE = re.compile(r"\(w\s*\.(\w+)\s*,\s*\.([CD])\)")


def scan_bit_theorems(path: Path | None = None) -> dict[str, dict[str, str]]:
    """Parse the per-bot `Phase.lean` files → `{lean_tmpl: {slot_tmpl: "C"|"D"}}`.

    Raises on structural surprises (wrong slot order, missing slots): a drifted
    source must fail loudly, never silently return a wrong table.
    """
    if path is not None:
        src = path.read_text()
    else:
        files = sorted(_workspace_root().glob(PHASE_GLOB))
        if not files:
            raise FileNotFoundError(f"no Phase.lean files match {PHASE_GLOB}")
        src = "\n".join(f.read_text() for f in files)
    tables: dict[str, dict[str, str]] = {}
    for m in _BITS_RE.finditer(src):
        _name, tmpl, entries_src = m.group(1), m.group(2), m.group(3)
        entries = _ENTRY_RE.findall(entries_src)
        slots = tuple(slot for slot, _ in entries)
        if slots != TAU_ORDER:
            raise ValueError(
                f"bit theorem for .{tmpl}: slots {slots} do not match tauOrder "
                f"{TAU_ORDER} — the Phase files drifted; update the scanner"
            )
        tables[tmpl] = {slot: action for slot, action in entries}
    if not tables:
        raise ValueError("no VoteBits theorems found — the Phase files drifted")
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
)
"""Canonical template order."""

BASE_OF: dict[str, str] = {
    "TauCooperate": "CooperateBot",
    "TauDefect": "DefectBot",
    "TauTFTSim": "TitForTatBot",
    "TauTFTPf": "TitForTatBot",
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
}
"""Which base bot each template lifts. The two TFT variants are two lift
MODALITIES of the same base strategy (behavioral vs prover); their bits coincide
on FLOOR-FREE columns only, which is why the prover twin carries whitelisted
divergences."""

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
    print("kernel bit tables (Tau/Theorems/*/Phase.lean, slot order = tauOrder):")
    for tmpl in TAU_ORDER:
        row = tables.get(tmpl)
        if row is None:
            print(f"  {tmpl:8s}  (no certified row)")
        else:
            print(f"  {tmpl:8s}  " + " ".join(row[s] for s in TAU_ORDER))


if __name__ == "__main__":
    main()

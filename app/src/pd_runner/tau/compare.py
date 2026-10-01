"""Def 3 ≡ Def 4 — the KERNEL-vs-BASE coincidence certification.

Under the corrected Def 4 (the uniform source lift, `Research/Notes/TAUBOTS.md`), the
two definitions threshold the SAME per-hypothesis bit at large k on terminating
cells — Def 3 reads it off the certified base matrix ("A's own action in
`outcome(A, Bᵢ)`"), Def 4 reads it off the compiled instance. So this module's job
is to CERTIFY agreement, not to hunt for separation. Any divergence on a
terminating cell at large k that is not one of the recorded artifacts below is a
BUG in one side, by definition.

**The check is MODEL-FREE (2026-08-24).** It reads Def 4's bits straight out of the
kernel-certified `VoteBits` theorems (`def4_theorems.kernel_bits`) and compares them
to the base matrix. The Python spec-mirror that used to re-derive those bits
(`def4.py`: the `LiftSpec` cascade interpreter, `decide`, and the phase sweep built
on them) is GONE — it was a second implementation of the Lean Spec DSL, and every
answer it produced was either confirmed by the kernel rows or unverifiable. Reading
the kernel directly removes the possibility of a shared bug in the model cancelling
out against itself, which the old three-check composition could only mitigate.

Consequences of that removal, stated plainly:

* Coverage is now exactly what Lean has STATED. A template with no `VoteBits`
  theorem is reported in `missing_rows` and compared nowhere — absence is the
  honest signal that a row is unproven, where the model would have predicted one.
  `TauDIMCID` is the live case.
* The (t, α) PHASE ATTRIBUTION sweep is gone with the model: it thresholded
  modelled Def-4 masses against Def-3 masses, and there is no kernel row for "the
  vote at α" to replace it with. The bit-level check is the stronger statement
  anyway — phases are a function of the bits.

The recorded divergences (`WHITELIST`) are properties of the LIFT, not of any
implementation: all six are budget-staggered dagger cells. `TauTFTPf` — the prover
reading of TitForTatBot's question — has no base bot and is compared nowhere
(2026-08-25); its divergence from `TauTFTSim` on floor-priced cooperation is the
prover/behavioral α-gap, reported by the kernel-row tests, not by this certification.

**Two sources (Phase 4 of `SPRIME_SOURCE_OF_TRUTH.md`, 2026-10-01).** The certification
runs on the matrix's OWN system: an engine matrix against `tau_rows.json`, a `S'` matrix
against `sprime_tau_rows.json` (`def4_theorems.TAU_EXPORTS`) — never crossed, since the
two systems' rows disagree at the DIMCID cells by theorem; a `S'` matrix with no `S'` row
file is still REFUSED (`SourceMismatchError`), never compared against the engine's rows.
On `S'` the scope is the 14 paper templates (`PAPER_TEMPLATES`, 196 cells on the 12 paper
base bots) and a cell has one of four fates, all counted separately: a THEOREM bit that
equals the base cell (agree), a FLOOR BIT that sits on a floor cell with the same
engine-side value (floor-agree — a dichotomy's `¬A_k` half on both sides, not a theorem
about the cell), a MISMATCH (different value, or a floor/theorem provenance swap between
the two exports), or UNCOVERED (the export is PARTIAL during the Phase-3 rollout: no bit
stated yet). On `S'` the RECORDED divergences
(`def4_theorems.SPRIME_RECORDED_DIVERGENCES`: the six floor bits on the tau images of the
red cell, a base theorem) are counted as whitelisted, like the engine's `WHITELIST`, and
printed as `~` lines; the certification passes "modulo recorded artifacts" and `mismatch`
counts only the unexpected. As of Phase 3e (2026-10-01): 195 covered = 148 agree +
41 floor-agree + 6 recorded, 0 mismatch, 1 uncovered (`dimcid × ebot`, UNSTATED in Lean:
`Tau/NeverFitsSys.lean`). The six VALUE divergences of Phases 3b–3d are gone (route (c)
made generic); a recorded entry that stops firing is reported by the loader
(`StaleDivergenceWarning`).
"""

from __future__ import annotations

from dataclasses import dataclass

from pd_runner.tau.def4_theorems import (
    BASE_OF,
    CONTROL_BOTS,
    LEAN_SLOT,
    PAPER_ORDER,
    PAPER_TEMPLATES,
    SEPARATING_BOTS,
    TAU_ORDER,
    TEMPLATES,
    kernel_bit_provenance,
    kernel_bits,
    recorded_divergence,
    tau_export_file,
)
from pd_runner.tau.matrix import TauMatrix

WHITELIST: dict[tuple[str, str], str] = {
    # EMPTY since 2026-08-27. Until then it held six budget-staggering cells — the base
    # matrix reported cooperation proved at a budget STAGGER (`PrudentBot (2k+64)` vs
    # `DupocBot k`, `JustBot (4j+100)` vs `CupodTrollBot j`, …) while the tau zoo runs
    # everyone at ONE shared budget. The base cells are now the shared-budget values
    # (`outcome_PrudentBot_vs_DupocBot = (D, D)`, `outcome_JustBot_vs_PrudentBot = (D, D)`,
    # `outcome_JustBot_vs_CupodTrollBot = (D, C)`, `outcome_DupocBot_vs_CupodTrollBot =
    # (D, C)`), the staggered results survive as `*_staggered` non-cell theorems, and
    # base and tau agree on every comparable cell (225/225/0).
}
"""The recorded bit divergences. Anything else is a bug by definition."""


# ── Check 1: the kernel check ──────────────────────────────────────────────────




# ── The certification: Lean's own bits vs the base matrix ─────────────────────


@dataclass(frozen=True)
class DirectCell:
    """One (tau bit as STATED IN LEAN) vs (base matrix cell) comparison."""

    template: str
    hypothesis: str
    lean: str
    """The bit read out of the Lean `RowSpec` row — the kernel's own answer."""
    base: str
    whitelisted: str | None
    lean_provenance: str = "theorem"
    """`"theorem"` (a RowSpec/RowSpecA slot), `"floor_dichotomy"` (a `S'` FloorBitA) or
    `"divergent"` (the engine's "N" fill)."""
    base_floor: bool = False
    """Whether the base cell is a `S'` floor dichotomy (`Cell.is_floor`)."""

    @property
    def lean_floor(self) -> bool:
        return self.lean_provenance == "floor_dichotomy"

    @property
    def provenance_swap(self) -> bool:
        """The two exports disagree on whether this cell is a floor — a mismatch even
        when the values agree (it can only mean the exports are out of step)."""
        return self.lean_floor != self.base_floor

    @property
    def agrees(self) -> bool:
        return self.lean == self.base and not self.provenance_swap

    @property
    def floor_agreement(self) -> bool:
        """A floor bit on a floor cell with the same engine-side value: both sides carry
        the `¬A_k` half of the same dichotomy — agreement, but not a theorem about the
        cell's value, so it is counted apart."""
        return self.agrees and self.lean_floor


@dataclass(frozen=True)
class DirectCoincidence:
    cells: tuple[DirectCell, ...]
    missing_rows: tuple[str, ...]
    """Templates with no stated Lean row, so nothing to compare."""
    uncovered: tuple[tuple[str, str], ...] = ()
    """(template, hypothesis) pairs whose base bots are in the matrix but for which the
    row file states no bit — a PARTIAL `S'` export: a stated row's missing slots AND
    every cell of a template with no row (those templates are also in `missing_rows`).
    Empty on the engine, whose stated rows are complete."""

    @property
    def agreements(self) -> int:
        """Every agreeing covered cell, floor agreements included."""
        return sum(1 for c in self.cells if c.agrees)

    @property
    def floor_agreements(self) -> int:
        return sum(1 for c in self.cells if c.floor_agreement)

    @property
    def theorem_agreements(self) -> int:
        return self.agreements - self.floor_agreements

    @property
    def unexpected(self) -> tuple[DirectCell, ...]:
        return tuple(c for c in self.cells if not c.agrees and c.whitelisted is None)

    @property
    def mismatches(self) -> int:
        return len(self.unexpected)

    @property
    def whitelisted_divergences(self) -> tuple[DirectCell, ...]:
        return tuple(c for c in self.cells if not c.agrees and c.whitelisted is not None)

    @property
    def covered(self) -> int:
        return len(self.cells)

    @property
    def total(self) -> int:
        """Covered + uncovered: the comparable cells of this roster."""
        return len(self.cells) + len(self.uncovered)

    @property
    def coverage_by_template(self) -> dict[str, tuple[int, int]]:
        """template → (covered, total) over this roster, in comparison order."""
        out: dict[str, list[int]] = {}
        for c in self.cells:
            out.setdefault(c.template, [0, 0])
            out[c.template][0] += 1
            out[c.template][1] += 1
        for a, _ in self.uncovered:
            out.setdefault(a, [0, 0])
            out[a][1] += 1
        order = {t: i for i, t in enumerate(TEMPLATES)}
        return {a: (out[a][0], out[a][1]) for a in sorted(out, key=lambda t: order.get(t, 99))}

    @property
    def complete(self) -> bool:
        """Every comparable cell has a stated bit (no partial rows, no missing rows)."""
        return not self.uncovered and not self.missing_rows

    @property
    def passed(self) -> bool:
        """No unexpected divergence on the COVERED cells (a partial export can pass on
        what it states; `complete` says whether it states everything)."""
        return bool(self.cells) and not self.unexpected


class SourceMismatchError(ValueError):
    """The certification was asked to compare the ENGINE's tau rows against a matrix
    read from another system."""


def _require_rows(matrix: TauMatrix) -> None:
    """A matrix is certified against ITS system's row file, never the other's: the engine's
    `tau_rows.json` and the `S'` `sprime_tau_rows.json` DISAGREE at the DIMCID cells by
    theorem. A `S'` matrix whose row file does not exist yet is refused — comparing it
    against the engine's rows would certify nothing."""
    if matrix.source == "engine":
        return
    export = tau_export_file(matrix.source)
    if not export.exists():
        raise SourceMismatchError(
            f"Def 3 ≡ Def 4 certification on source={matrix.source!r}: no S' tau rows exist "
            f"yet ({export} not found — Phase 4 of SPRIME_SOURCE_OF_TRUTH.md reads the file "
            "`lake exe export_sprime_outcomes` writes), and the engine's `tau_rows.json` "
            "disagrees with S' at the DIMCID cells, so it is not consulted. Generate the "
            "S' rows, or load the matrix with source=\"engine\" (CLI: --source engine)."
        )


def templates_for(source: str) -> tuple[str, ...]:
    """The certification's scope per source: every template on the engine, the 14 paper
    templates (`paperOrder`) on `S'`."""
    return TEMPLATES if source == "engine" else PAPER_TEMPLATES


def direct_kernel_vs_base(
    matrix: TauMatrix, templates: tuple[str, ...] | None = None
) -> DirectCoincidence:
    """Lean's OWN bit rows against the base matrix — the whole certification.

    Restricted to the templates whose base bots are in `matrix` (default scope per
    source: `templates_for`), so the caller's zoo choice decides coverage; rows Lean
    has not stated are reported rather than guessed, and on `S'` a stated row's missing
    slots are reported as `uncovered`. The base side is the BASE CELL (`matrix.action`,
    Def 3), not `test_bit` — which would read the kernel row back. The matrix is
    compared against ITS system's row file (`_require_rows`).
    """
    _require_rows(matrix)
    if templates is None:
        templates = templates_for(matrix.source)
    tables = kernel_bits(source=matrix.source)
    provenance = kernel_bit_provenance(source=matrix.source)
    template_of_slot = {v: k for k, v in LEAN_SLOT.items()}
    order = TAU_ORDER if matrix.source == "engine" else PAPER_ORDER

    cells: list[DirectCell] = []
    uncovered: list[tuple[str, str]] = []
    for A in templates:
        row = tables.get(LEAN_SLOT[A])
        for T in templates:
            base_a, base_t = BASE_OF.get(A), BASE_OF.get(T)
            # a template with no base bot (TauTFTPf) is compared nowhere
            if base_a is None or base_t is None:
                continue
            if base_a not in matrix.bots or base_t not in matrix.bots:
                continue
            # no row at all (also in `missing_rows`) or a partial row: uncovered
            lean_bit = row.get(LEAN_SLOT[T]) if row is not None else None
            if lean_bit is None:
                uncovered.append((A, T))
                continue
            # A proven-`none` base outcome is the fifth state "N", and the kernel
            # reports a divergent tau diagonal the same way — so the two can
            # AGREE there, rather than the comparison inventing a D on one side.
            base_cell = matrix.cell(base_a, base_t)
            # the engine's WHITELIST (empty), or on S' a RECORDED Def 3 ≢ Def 4 bit
            rec = recorded_divergence(matrix.source, LEAN_SLOT[A], LEAN_SLOT[T])
            cells.append(
                DirectCell(
                    template=A,
                    hypothesis=T,
                    lean=lean_bit,
                    base=matrix.action(base_a, base_t),
                    whitelisted=WHITELIST.get((A, T)) or (
                        f"recorded {rec.kind} divergence: {rec.reason}" if rec else None),
                    lean_provenance=provenance.get(LEAN_SLOT[A], {}).get(LEAN_SLOT[T], "theorem"),
                    base_floor=base_cell.is_floor,
                )
            )
    missing = tuple(
        template_of_slot[s]
        for s in order
        if s not in tables and template_of_slot[s] in templates
        and template_of_slot[s] in BASE_OF
    )
    return DirectCoincidence(cells=tuple(cells), missing_rows=missing, uncovered=tuple(uncovered))


# ── The certification bundle ───────────────────────────────────────────────────


@dataclass(frozen=True)
class Certification:
    direct: DirectCoincidence
    """Lean's own bits vs the base matrix — the model-free end-to-end check."""
    zoo_name: str

    @property
    def passed(self) -> bool:
        return self.direct.passed


def certify(
    matrix: TauMatrix,
    zoo_name: str,
    templates: tuple[str, ...] | None = None,
) -> Certification:
    return Certification(
        direct=direct_kernel_vs_base(matrix, templates),
        zoo_name=zoo_name,
    )


def render(cert: Certification) -> str:
    lines: list[str] = []
    lines.append(f"Def 3 ≡ Def 4 coincidence certification — zoo: {cert.zoo_name}")
    lines.append("(all tables at LARGE k, past the Löb threshold)")
    lines.append("")
    d = cert.direct
    lines.append(
        f"KERNEL vs BASE (model-free): {d.agreements}/{len(d.cells)} agree; "
        f"{len(d.whitelisted_divergences)} whitelisted; "
        f"{len(d.unexpected)} unexpected "
        + ("— OK" if d.passed else "— FAILED")
    )
    lines.append(
        f"   agree (theorem bits): {d.theorem_agreements}   floor-agree (dichotomy bits): "
        f"{d.floor_agreements}   mismatch: {d.mismatches}   uncovered: {len(d.uncovered)}"
        f"   [covered {d.covered}/{d.total}]"
    )
    cov = d.coverage_by_template
    if cov:
        lines.append(
            "   coverage per template: "
            + ", ".join(f"{a} {c}/{t}" for a, (c, t) in cov.items())
        )
    if d.missing_rows:
        lines.append(
            "   (rows not yet stated in Lean, so not compared: "
            + ", ".join(d.missing_rows) + ")"
        )
    for c in d.whitelisted_divergences:
        lines.append(
            f"   ~ ({c.template}, {c.hypothesis}): lean {c.lean} vs base {c.base}"
            f" [{c.whitelisted}]"
        )
    for c in d.unexpected:
        why = (" (floor/theorem provenance swap)" if c.provenance_swap and c.lean == c.base
               else "")
        lines.append(
            f"   ✗ ({c.template}, {c.hypothesis}): lean {c.lean} vs base {c.base}{why}"
        )
    lines.append("")
    verdict = ("COINCIDE (modulo recorded artifacts) ✓" if cert.passed
               else "DIVERGENCE — a bug in one side, by definition ✗")
    if cert.passed and not d.complete:
        verdict += f" — PARTIAL: {len(d.uncovered)} cell(s) not yet stated"
    lines.append("VERDICT: " + verdict)
    return "\n".join(lines)


def main() -> None:
    import argparse
    import sys

    from pd_runner.tau.matrix import PAPER_TWINS_SUB_ZOO, load_tau_matrix

    from pd_runner import settings

    parser = argparse.ArgumentParser(
        description="Certify Def 3 ≡ Def 4 at large k, straight from the kernel."
    )
    parser.add_argument("--zoo", choices=("control", "separating", "paper"), default="separating",
                        help="`paper` = the 12 paper base bots: on `sprime` the full "
                             "196-cell table of the 14 paper templates")
    parser.add_argument("--source", choices=list(settings.CELL_SOURCES), default=None,
                        help=(f"cell source (default: {settings.CELL_SOURCE}); the matrix is "
                              "certified against ITS system's row file (tau_rows.json / "
                              "sprime_tau_rows.json)"))
    args = parser.parse_args()

    bots = {"control": CONTROL_BOTS, "separating": SEPARATING_BOTS,
            "paper": PAPER_TWINS_SUB_ZOO}[args.zoo]
    matrix = load_tau_matrix(bots, source=args.source)
    try:
        cert = certify(matrix, args.zoo)
    except SourceMismatchError as exc:
        print(f"REFUSED: {exc}")
        sys.exit(2)
    print(render(cert))
    sys.exit(0 if cert.passed else 1)


if __name__ == "__main__":
    main()

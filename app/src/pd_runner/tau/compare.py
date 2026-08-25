"""Def 3 ≡ Def 4 — the KERNEL-vs-BASE coincidence certification.

Under the corrected Def 4 (the uniform source lift, `DEF4_TVOTE_ROADMAP.md`), the
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
"""

from __future__ import annotations

from dataclasses import dataclass

from pd_runner.tau.def4_theorems import (
    BASE_OF,
    CONTROL_BOTS,
    LEAN_SLOT,
    SEPARATING_BOTS,
    TAU_ORDER,
    TEMPLATES,
    kernel_bits,
)
from pd_runner.tau.matrix import TauMatrix

WHITELIST: dict[tuple[str, str], str] = {
    # Every entry is BUDGET STAGGERING, and since 2026-08-25 every one is certified
    # on BOTH sides in base: the strict `outcome_{L}_vs_{R}` theorem proves the
    # cooperative cell at a budget stagger (the extra budget pays a partner's
    # `search_f` floor), and the `_samek` theorem proves the tau value at ONE shared
    # budget — exactly what `tauZoo k` gives every bot. Base and tau agree on the
    # mathematics; the certification compares against the strict (staggered) cell.
    ("TauDupoc", "TauCupodTroll"): (
        "Budget staggering. `outcome_CupodTrollBot_vs_DupocBot` is (C, C) under "
        "`hjk` (DupocBot's budget above Troll's failed identity search); at one "
        "budget Troll's C is its else-play and Dupoc defects — "
        "`outcome_DupocBot_vs_CupodTrollBot_samek = (D, C)`."
    ),
    ("TauJust", "TauCupodTroll"): (
        "Budget staggering. `outcome_JustBot_vs_CupodTrollBot` is (C, C) at "
        "JustBot (4j+100); at one budget Just's probe of Troll's floor-priced C "
        "fails — `outcome_JustBot_vs_CupodTrollBot_samek = (D, C)`."
    ),
    ("TauPrudent", "TauDupoc"): (
        "Budget staggering. `outcome_PrudentBot_vs_DupocBot` is (C, C) at "
        "PrudentBot (2k+64); at one budget Prudent's inner check on Dupoc's "
        "else-play D fails — `outcome_PrudentBot_vs_DupocBot_samek = (D, D)`."
    ),
    ("TauDupoc", "TauPrudent"): (
        "Budget staggering, the other orientation of (TauPrudent, TauDupoc): "
        "Dupoc's probe of Prudent fails by soundness once Prudent defects — "
        "`outcome_PrudentBot_vs_DupocBot_samek = (D, D)`."
    ),
    ("TauPrudent", "TauJust"): (
        "Budget staggering. `outcome_JustBot_vs_PrudentBot` is (C, C) at "
        "PrudentBot (2k+64); at one budget Prudent's inner check on the frozen "
        "Dupoc's else-play D fails — `outcome_JustBot_vs_PrudentBot_samek = (D, D)`."
    ),
    ("TauJust", "TauPrudent"): (
        "Budget staggering, the other orientation of (TauPrudent, TauJust): "
        "Just's probe of Prudent's cooperation with the frozen Dupoc fails by "
        "soundness — `outcome_JustBot_vs_PrudentBot_samek = (D, D)`."
    ),
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
    """The bit read out of the Lean `VoteBits` row — the kernel's own answer."""
    base: str
    whitelisted: str | None

    @property
    def agrees(self) -> bool:
        return self.lean == self.base


@dataclass(frozen=True)
class DirectCoincidence:
    cells: tuple[DirectCell, ...]
    missing_rows: tuple[str, ...]
    """Templates with no stated Lean row, so nothing to compare."""

    @property
    def agreements(self) -> int:
        return sum(1 for c in self.cells if c.agrees)

    @property
    def unexpected(self) -> tuple[DirectCell, ...]:
        return tuple(c for c in self.cells if not c.agrees and c.whitelisted is None)

    @property
    def whitelisted_divergences(self) -> tuple[DirectCell, ...]:
        return tuple(c for c in self.cells if not c.agrees and c.whitelisted is not None)

    @property
    def passed(self) -> bool:
        return bool(self.cells) and not self.unexpected


def direct_kernel_vs_base(
    matrix: TauMatrix, templates: tuple[str, ...] = TEMPLATES
) -> DirectCoincidence:
    """Lean's OWN bit rows against the base matrix — the whole certification.

    Restricted to the templates whose base bots are in `matrix`, so the caller's
    zoo choice decides coverage; rows Lean has not stated are reported rather
    than guessed.
    """
    tables = kernel_bits()
    template_of_slot = {v: k for k, v in LEAN_SLOT.items()}

    cells: list[DirectCell] = []
    for A in templates:
        row = tables.get(LEAN_SLOT[A])
        if row is None:
            continue
        for T in templates:
            lean_bit = row.get(LEAN_SLOT[T])
            if lean_bit is None:
                continue
            base_a, base_t = BASE_OF.get(A), BASE_OF.get(T)
            # a template with no base bot (TauTFTPf) is compared nowhere
            if base_a is None or base_t is None:
                continue
            if base_a not in matrix.bots or base_t not in matrix.bots:
                continue
            # A proven-`none` base outcome is the fifth state "N", and the kernel
            # reports a divergent tau diagonal the same way — so the two can
            # AGREE there, rather than the comparison inventing a D on one side.
            base_cell = matrix.cell(base_a, base_t)
            base_bit = (
                "N" if base_cell.shape == "no_outcome"
                else ("C" if matrix.cooperates(base_a, base_t) else "D")
            )
            cells.append(
                DirectCell(
                    template=A,
                    hypothesis=T,
                    lean=lean_bit,
                    base=base_bit,
                    whitelisted=WHITELIST.get((A, T)),
                )
            )
    missing = tuple(
        template_of_slot[s]
        for s in TAU_ORDER
        if s not in tables and template_of_slot[s] in templates
        and template_of_slot[s] in BASE_OF
    )
    return DirectCoincidence(cells=tuple(cells), missing_rows=missing)


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
    templates: tuple[str, ...] = TEMPLATES,
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
        lines.append(
            f"   ✗ ({c.template}, {c.hypothesis}): lean {c.lean} vs base {c.base}"
        )
    lines.append("")
    lines.append("VERDICT: " + ("COINCIDE (modulo recorded artifacts) ✓" if cert.passed
                                else "DIVERGENCE — a bug in one side, by definition ✗"))
    return "\n".join(lines)


def main() -> None:
    import argparse
    import sys

    from pd_runner.tau.matrix import load_tau_matrix

    parser = argparse.ArgumentParser(
        description="Certify Def 3 ≡ Def 4 at large k, straight from the kernel."
    )
    parser.add_argument("--zoo", choices=("control", "separating"), default="separating")
    args = parser.parse_args()

    bots = CONTROL_BOTS if args.zoo == "control" else SEPARATING_BOTS
    matrix = load_tau_matrix(bots)
    cert = certify(matrix, args.zoo)
    print(render(cert))
    sys.exit(0 if cert.passed else 1)


if __name__ == "__main__":
    main()

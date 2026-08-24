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
implementation: the Mirror-branch truncation, the prover-modality floors, and the
budget-staggered dagger cells.
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
    # ("TauEBot", "TauEBot") — REMOVED 2026-08-24. The entry read "Mirror-branch
    # truncation: base EBot's third branch sims MirrorBot (not .opp-free-liftable);
    # the lift drops it, flipping E's self-bit". It was a COVERAGE gap, not a
    # property of the lift: MirrorBot IS liftable — `.sim .opp .self` becomes a
    # `run` stage on the SELF target, copying in the frozen self frame. With
    # `.mirror` in the roster EBot's third stage is expressible again, its self
    # watch fires, and the cell AGREES with base `outcome_EBot_vs_EBot = (C, C)`.
    ("TauTFTPf", "TauCupodTroll"): (
        "Floor over true cooperation: τ(CupodTroll)'s C is reached through a "
        "FAILED .eq search, so its transcript pays search_f and no prover can "
        "cite it at the SAME budget. Base TitForTatBot is the BEHAVIORAL bot "
        "(it sims, so it sees the C); its prover lift cannot. A genuine "
        "modality difference — the α-gap."
    ),
    ("TauDupoc", "TauCupodTroll"): (
        "**BUDGET STAGGERING, not a modality gap.** Base "
        "`outcome_CupodTrollBot_vs_DupocBot` really is (C, C) — but it is a "
        "DAGGER cell, proven only under the side hypothesis `hjk`, which gives "
        "DupocBot a budget strictly larger than Troll's failed search "
        "(`|¬(Dupoc = Cupod)| + j + 2 ≤ k`). Paying Troll's search_f floor is "
        "exactly what that buys. The tau layer gives EVERY bot the same budget "
        "`k` (`tauZoo k`), so the staggering is unavailable by construction and "
        "the prove-stage honestly reads 0. Base and tau agree on the "
        "mathematics and differ on the budget regime."
    ),
    ("TauJust", "TauCupodTroll"): (
        "Budget staggering — same as (TauDupoc, TauCupodTroll). Base "
        "`outcome_JustBot_vs_CupodTrollBot` is stated at JustBot (4*j+100) vs "
        "CupodTrollBot j: the 4x+100 stagger is what affords Troll's floor. "
        "Same-k tau cannot reproduce it."
    ),
    # ── prover-modality floors, 3rd and 4th floor bots (2026-08-24) ──────────
    # The whitelist was written when the zoo had TWO floor bots (Guardian,
    # CupodTroll). Cupod and DIMCID are the third and fourth, added later, and
    # produce the identical divergence against the PROVER TFT.
    ("TauTFTPf", "TauCupod"): (
        "Prover-modality floor, same shape as (TauTFTPf, TauGuardian): "
        "τ(Cupod)'s C is the ELSE-play of a failed punish-search, so its "
        "transcript pays search_f and no prover can cite it at the same budget "
        "(`ps_probe_inst_cupod_coop_false`). Base TitForTatBot is the "
        "BEHAVIORAL bot — it sims and sees the C; its prover lift cannot."
    ),
    ("TauTFTPf", "TauDIMCID"): (
        "Prover-modality floor — τ(DIMCID) is the zoo's FOURTH floor bot. Its C "
        "is the else-play of a failed impl-guard search "
        "(`ps_probe_inst_dimcid_coop_false`; the base twin is "
        "`no_provable_DIMCID_C_tail`), so the prover TFT reads 0 where the "
        "behavioral base TFT sims a C."
    ),
    # The two (TauCupodTroll, TauCupod) entries recorded here on 2026-08-24 were
    # REMOVED the same day: the divergence was a COMPILER BUG, not a property of
    # the lift. `proveEq` emitted `.eq .opp (.bot (inst T B))` — a free pronoun
    # against a counterfactual probe — so the guard could never fire. Restating it
    # as "is the signal I am treating the lift of B?" made both cells AGREE with
    # base. A whitelist entry describing a fixable defect is a rug; the fix is in
    # `Tau/Spec.lean`.
    ("TauTFTPf", "TauGuardian"): (
        "Prover-modality floor: TauTFTPf is the PROVER variant of behavioral base "
        "TFT, and Guardian's cooperation is floor-priced — true (base TFT sims it: "
        "C) but unprovable at every budget (the prover twin reads D). The α-gap "
        "headline as a bit-level divergence."
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
            base_a, base_t = BASE_OF[A], BASE_OF[T]
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

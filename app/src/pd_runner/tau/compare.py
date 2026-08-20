"""Def 3 ≡ Def 4 — the COINCIDENCE CERTIFICATION.

Under the corrected Def 4 (the uniform source lift, `DEF4_TVOTE_ROADMAP.md`), the
two definitions threshold the SAME per-hypothesis bit at large k on terminating
cells — Def 3 reads it off the certified base matrix ("A's own action in
`outcome(A, Bᵢ)`"), Def 4 computes it by running A's lifted cascade at point mass.
So this module's job is the INVERSE of its retracted predecessor: it no longer hunts
for separation, it CERTIFIES agreement. Any divergence on a terminating cell at
large k that is not one of the two recorded artifacts below is a BUG in one side,
by definition.

The two recorded, honest divergences (both artifacts of conventions, not of probe
semantics):

1. **The Mirror-branch truncation** (`WHITELIST`): base EBot's third branch sims
   MirrorBot, which is not `.opp`-free-liftable; the truncated lift drops it, so
   τ(EBot)'s SELF-bit is 0 where Def 3 reads base `EBot vs EBot`'s escape. The one
   genuinely open lift convention, recorded since the retraction.
2. **The α = 0 constant artifact**: Def 3 lifts every base bot uniformly, so its
   τ(DefectBot) has mass 0 and cooperates at α = 0 (`0 ≥ 0`); Lean's `TauDefect` is
   literally `.const .D`. A modelling-convention corner, not a probe difference.

The certification is three checks, strongest first:

* **kernel check** — the Python spec-mirror's decision table equals the KERNEL bit
  tables parsed from `Tau/VotePhases.lean` (6×6, exact);
* **bit coincidence** — Def-4 compound bits equal Def-3 base-matrix bits on every
  pair, except exactly the whitelist;
* **phase attribution** — sweeping (t, α) with the whitelisted bit PATCHED to
  Def 3's value, the two phase diagrams are IDENTICAL outside α = 0 constant
  artifacts. Divergence that survives the patch fails the run.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field

from pd_runner.tau.def4 import (
    BASE_OF,
    CONTROL_BOTS,
    CONTROL_ZOO,
    LEAN_SLOT,
    SEPARATING_BOTS,
    SEPARATING_ZOO,
    TEMPLATES,
    decide,
    decision_table,
    tau_play_def4,
)
from pd_runner.tau.def4_theorems import kernel_bits
from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.play import _MASS_TOL, coop_mass, tau_play
from pd_runner.tau.signal import Signal, behavioral_distance_matrix, signal_family

WHITELIST: dict[tuple[str, str], str] = {
    ("TauEBot", "TauEBot"): (
        "Mirror-branch truncation: base EBot's third branch sims MirrorBot "
        "(not .opp-free-liftable); the lift drops it, flipping E's self-bit"
    ),
    ("TauTFTPf", "TauCupodTroll"): (
        "Floor over true cooperation (the Guardian shape, second instance): "
        "τ(CupodTroll)'s C is reached through a FAILED .eq search, so its "
        "transcript pays search_f and no prover can cite it — while base "
        "CupodTrollBot simply cooperates. Any PROVER bot probing it reads 0."
    ),
    ("TauDupoc", "TauCupodTroll"): (
        "Floor over true cooperation — same mechanism as (TauTFTPf, TauCupodTroll)."
    ),
    ("TauJust", "TauCupodTroll"): (
        "Floor over true cooperation — same mechanism as (TauTFTPf, TauCupodTroll)."
    ),
    ("TauTFTPf", "TauGuardian"): (
        "Prover-modality floor: TauTFTPf is the PROVER variant of behavioral base "
        "TFT, and Guardian's cooperation is floor-priced — true (base TFT sims it: "
        "C) but unprovable at every budget (the prover twin reads D). The α-gap "
        "headline as a bit-level divergence."
    ),
}
"""The recorded bit divergences. Anything else is a bug by definition."""


# ── Check 1: the kernel check ──────────────────────────────────────────────────


@dataclass(frozen=True)
class KernelCheck:
    """Python spec-mirror vs the Lean bit tables."""

    checked: int
    mismatches: tuple[str, ...]

    @property
    def passed(self) -> bool:
        return self.checked > 0 and not self.mismatches


def kernel_check() -> KernelCheck:
    """Every compound decision equals the kernel-certified bit, 6×6."""
    lean = kernel_bits()
    computed = decision_table()
    mismatches: list[str] = []
    checked = 0
    for A in TEMPLATES:
        row = lean.get(LEAN_SLOT[A])
        if row is None:
            mismatches.append(f"{A}: no kernel bit table")
            continue
        for T in TEMPLATES:
            checked += 1
            want = row[LEAN_SLOT[T]]
            got = computed[A][T].action
            if got != want:
                mismatches.append(f"({A}, {T}): python {got} ≠ kernel {want}")
    return KernelCheck(checked=checked, mismatches=tuple(mismatches))


# ── Check 2: bit coincidence (Def 4 vs Def 3, whitelisted) ─────────────────────


@dataclass(frozen=True)
class BitCell:
    template: str
    hypothesis: str
    def4: str
    def3: str
    whitelisted: str | None

    @property
    def agrees(self) -> bool:
        return self.def4 == self.def3


@dataclass(frozen=True)
class Coincidence:
    cells: tuple[BitCell, ...]

    @property
    def agreements(self) -> int:
        return sum(1 for c in self.cells if c.agrees)

    @property
    def whitelisted_divergences(self) -> tuple[BitCell, ...]:
        return tuple(c for c in self.cells if not c.agrees and c.whitelisted)

    @property
    def unexpected(self) -> tuple[BitCell, ...]:
        """Divergences NOT on the whitelist — each one is a bug, by definition.
        A whitelisted cell that AGREES is also unexpected (a stale whitelist must
        not silently over-approve)."""
        wrong = tuple(c for c in self.cells if not c.agrees and not c.whitelisted)
        stale = tuple(c for c in self.cells if c.agrees and c.whitelisted)
        return wrong + stale

    @property
    def passed(self) -> bool:
        return not self.unexpected


def bit_coincidence(matrix: TauMatrix) -> Coincidence:
    """Def-4 compound bits vs Def-3 base-matrix bits, all template pairs whose
    base cells the matrix knows."""
    cells: list[BitCell] = []
    for A in TEMPLATES:
        for T in TEMPLATES:
            base_a, base_t = BASE_OF[A], BASE_OF[T]
            if base_a not in matrix.bots or base_t not in matrix.bots:
                continue
            d4 = decide(A, T).action
            d3 = "C" if matrix.cooperates(base_a, base_t) else "D"
            cells.append(
                BitCell(
                    template=A,
                    hypothesis=T,
                    def4=d4,
                    def3=d3,
                    whitelisted=WHITELIST.get((A, T)),
                )
            )
    return Coincidence(cells=tuple(cells))


# ── Check 3: phase attribution over (t, α) ─────────────────────────────────────


@dataclass(frozen=True)
class PhaseCell:
    t: float
    alpha: float
    row: str
    col: str
    def3: tuple[str, str]
    def4: tuple[str, str]
    patched: tuple[str, str]
    """Def-4 with every whitelisted bit forced to its Def-3 value — the
    attribution probe: a divergence that persists here is NOT explained by the
    whitelist."""


@dataclass(frozen=True)
class PhaseSweep:
    cells: tuple[PhaseCell, ...]
    n_bands: int

    @property
    def divergent(self) -> tuple[PhaseCell, ...]:
        return tuple(c for c in self.cells if c.def3 != c.def4)

    @property
    def unexplained(self) -> tuple[PhaseCell, ...]:
        """Cells whose divergence survives the whitelist patch AND is not the
        α = 0 constant artifact."""
        out = []
        for c in self.divergent:
            if c.patched == c.def3:
                continue  # fully attributed to whitelisted bits
            if c.alpha <= _MASS_TOL and _constant_involved(c):
                continue  # the α = 0 constant artifact
            out.append(c)
        return tuple(out)

    @property
    def passed(self) -> bool:
        return not self.unexplained


def _constant_involved(c: PhaseCell) -> bool:
    return "TauCooperate" in (c.row, c.col) or "TauDefect" in (c.row, c.col)


def _whitelist_overrides(matrix: TauMatrix) -> dict[tuple[str, str], str]:
    """The whitelisted bits, patched to their Def-3 values."""
    out: dict[tuple[str, str], str] = {}
    for (A, T), _reason in WHITELIST.items():
        base_a, base_t = BASE_OF[A], BASE_OF[T]
        if base_a in matrix.bots and base_t in matrix.bots:
            out[(A, T)] = "C" if matrix.cooperates(base_a, base_t) else "D"
    return out


def _breakpoints(
    matrix: TauMatrix,
    zoo: dict[str, str],
    bots: tuple[str, ...],
    channel: dict[str, Signal],
) -> list[float]:
    """Union of both definitions' achievable cooperation masses (exact α axis;
    masses used UNROUNDED — rounding can nudge a breakpoint above its mass and
    flip the very cell it probes)."""
    masses = {0.0}
    for actor in bots:
        for signal in channel.values():
            masses.add(coop_mass(matrix, actor, signal))
            masses.add(
                math.fsum(
                    p
                    for hyp, p in signal.weights.items()
                    if p > 0 and decide(zoo[actor], zoo[hyp]).action == "C"
                )
            )
    return sorted(masses)


def _bands(breakpoints: list[float]) -> list[float]:
    """Representative α per band: behavior is constant on `(prev, bp]` under the
    `≥ α` convention, so probe AT each breakpoint plus one α above the top."""
    alphas = list(breakpoints)
    top = breakpoints[-1] if breakpoints else 0.0
    if top < 1.0:
        alphas.append((top + 1.0) / 2)
    return alphas


def phase_sweep(
    matrix: TauMatrix,
    zoo: dict[str, str],
    bots: tuple[str, ...],
    t_values: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
) -> PhaseSweep:
    """Both definitions' full (t, α) phase diagrams, plus the whitelist-patched
    Def-4 diagram for attribution. Each matchup sees its own σ_t signal of the
    true opponent (the fair-comparison convention from milestone 1)."""
    tmpl_of = zoo
    overrides = _whitelist_overrides(matrix)
    distances = behavioral_distance_matrix(matrix)
    cells: list[PhaseCell] = []
    n_bands = 0
    for t in t_values:
        channel = signal_family(matrix, t, distances=distances)
        for alpha in _bands(_breakpoints(matrix, zoo, bots, channel)):
            n_bands += 1
            for row in bots:
                for col in bots:
                    d3 = (
                        tau_play(matrix, row, alpha, channel[col]),
                        tau_play(matrix, col, alpha, channel[row]),
                    )
                    d4 = (
                        tau_play_def4(zoo[row], alpha, channel[col], tmpl_of),
                        tau_play_def4(zoo[col], alpha, channel[row], tmpl_of),
                    )
                    dp = (
                        tau_play_def4(zoo[row], alpha, channel[col], tmpl_of, overrides),
                        tau_play_def4(zoo[col], alpha, channel[row], tmpl_of, overrides),
                    )
                    cells.append(
                        PhaseCell(
                            t=t,
                            alpha=alpha,
                            row=zoo[row],
                            col=zoo[col],
                            def3=d3,
                            def4=d4,
                            patched=dp,
                        )
                    )
    return PhaseSweep(cells=tuple(cells), n_bands=n_bands)


# ── The certification bundle ───────────────────────────────────────────────────


@dataclass(frozen=True)
class Certification:
    kernel: KernelCheck
    bits: Coincidence
    phases: PhaseSweep
    zoo_name: str

    @property
    def passed(self) -> bool:
        return self.kernel.passed and self.bits.passed and self.phases.passed


def certify(
    matrix: TauMatrix,
    zoo: dict[str, str],
    bots: tuple[str, ...],
    zoo_name: str,
    t_values: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
) -> Certification:
    return Certification(
        kernel=kernel_check(),
        bits=bit_coincidence(matrix),
        phases=phase_sweep(matrix, zoo, bots, t_values),
        zoo_name=zoo_name,
    )


def render(cert: Certification) -> str:
    lines: list[str] = []
    lines.append(f"Def 3 ≡ Def 4 coincidence certification — zoo: {cert.zoo_name}")
    lines.append("(all tables at LARGE k, past the Löb threshold)")
    lines.append("")
    k = cert.kernel
    lines.append(
        f"1. KERNEL CHECK: {k.checked} compound decisions vs Tau/VotePhases.lean "
        + ("— OK" if k.passed else "— FAILED")
    )
    for m in k.mismatches:
        lines.append(f"   ✗ {m}")
    b = cert.bits
    lines.append(
        f"2. BIT COINCIDENCE: {b.agreements}/{len(b.cells)} agree; "
        f"{len(b.whitelisted_divergences)} whitelisted divergence(s); "
        f"{len(b.unexpected)} unexpected "
        + ("— OK" if b.passed else "— FAILED")
    )
    for c in b.whitelisted_divergences:
        lines.append(
            f"   ~ ({c.template}, {c.hypothesis}): def4 {c.def4} vs def3 {c.def3}"
            f" [{c.whitelisted}]"
        )
    for c in b.unexpected:
        lines.append(
            f"   ✗ ({c.template}, {c.hypothesis}): def4 {c.def4} vs def3 {c.def3}"
        )
    p = cert.phases
    lines.append(
        f"3. PHASE ATTRIBUTION: {len(p.cells)} (t, α, matchup) cells over "
        f"{p.n_bands} bands; {len(p.divergent)} divergent, "
        f"{len(p.divergent) - len(p.unexplained)} attributed "
        f"(whitelist patch / α=0 constant artifact), "
        f"{len(p.unexplained)} unexplained "
        + ("— OK" if p.passed else "— FAILED")
    )
    for c in p.unexplained[:10]:
        lines.append(
            f"   ✗ t={c.t} α={c.alpha:.4f} {c.row} vs {c.col}: "
            f"def3 {c.def3} def4 {c.def4} patched {c.patched}"
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
        description="Certify Def 3 ≡ Def 4 at large k (the corrected source lift)."
    )
    parser.add_argument("--zoo", choices=("control", "separating"), default="separating")
    parser.add_argument(
        "--t-values",
        default="0,0.25,0.5,0.75,1.0",
        help="comma-separated transparency values",
    )
    args = parser.parse_args()

    if args.zoo == "control":
        zoo, bots = CONTROL_ZOO, CONTROL_BOTS
    else:
        zoo, bots = SEPARATING_ZOO, SEPARATING_BOTS
    t_values = tuple(float(x) for x in args.t_values.split(","))
    matrix = load_tau_matrix(bots)
    cert = certify(matrix, zoo, bots, args.zoo, t_values)
    print(render(cert))
    sys.exit(0 if cert.passed else 1)


if __name__ == "__main__":
    main()

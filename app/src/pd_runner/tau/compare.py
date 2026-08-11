"""Def 3 vs Def 4 — side-by-side (t, α) outcome matrices.

Runs the SAME tournament twice over the same certified base matrix, the same
σ_t channel and the same α grid, changing only the probe semantics:

  * Def 3 (`play.tau_match`)  — the self-probe lift, every bot.
  * Def 4 (`def4.tau_play_def4`) — per-bot probe geometry (reciprocity for
    TauDupoc, third-party for the TFTs), matching the Lean zoo.

Both sides see the matchup's OWN signal `σ_t(true opponent)`, so the
information structure is identical and any difference isolates to the probe.
This matters: our Lean Def-4 bots carry one STATIC weight vector, and comparing
that directly against Def 3's correlated signals would show a difference at
t = 1 that is an artefact of the signal model, not of the definition. The Lean
phase theorems quantify over arbitrary weights, so instantiating them per
matchup is faithful.

The α axis is exact, not sampled: the phase diagram is piecewise constant with
breakpoints at the achievable cooperation masses, so we enumerate the union of
both definitions' breakpoints and report one matrix per α band.

**Budget caveat.** Every table is at LARGE `k` — past the Löb threshold, where
the Lean theorems live. The sub-Löb regime (TauDupoc's self-bit off) is not
covered by any theorem and is not modelled.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

from pd_runner.tau.def4 import CONTROL_ZOO, Def4Bot, coop_mass_def4, probe_bit
from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.play import _MASS_TOL, coop_mass
from pd_runner.tau.signal import Signal, behavioral_distance_matrix, signal_family

# The comparison zoo: the four base bots whose tau lifts we compare. Kept
# separate from `def4.CONTROL_ZOO` (which maps them to probe geometries) so the
# ORDER is fixed for presentation.
COMPARISON_BOTS: tuple[str, ...] = (
    "DupocBot",
    "CooperateBot",
    "DefectBot",
    "TitForTatBot",
)


@dataclass(frozen=True)
class CellPair:
    """One matchup under both definitions."""

    row: str
    col: str
    def3: tuple[str, str]
    def4: tuple[str, str]

    @property
    def agrees(self) -> bool:
        return self.def3 == self.def4


@dataclass(frozen=True)
class Comparison:
    """Both definitions' full outcome matrices at one (t, α)."""

    t: float
    alpha: float
    cells: tuple[CellPair, ...]

    @property
    def agrees(self) -> bool:
        return all(c.agrees for c in self.cells)

    @property
    def disagreements(self) -> tuple[CellPair, ...]:
        return tuple(c for c in self.cells if not c.agrees)

    def matrix(self, which: str) -> dict[tuple[str, str], tuple[str, str]]:
        return {(c.row, c.col): (c.def3 if which == "def3" else c.def4) for c in self.cells}


def def3_actions(
    matrix: TauMatrix,
    row: str,
    col: str,
    alpha: float,
    channel: dict[str, Signal],
) -> tuple[str, str]:
    """Def 3: each side votes on its own action against the hypotheses."""
    row_mass = coop_mass(matrix, row, channel[col])
    col_mass = coop_mass(matrix, col, channel[row])
    return (
        "C" if row_mass >= alpha - _MASS_TOL else "D",
        "C" if col_mass >= alpha - _MASS_TOL else "D",
    )


def def4_actions(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot],
    row: str,
    col: str,
    alpha: float,
    channel: dict[str, Signal],
) -> tuple[str, str]:
    """Def 4: each side votes on ITS OWN probe geometry."""
    row_mass = coop_mass_def4(matrix, zoo[row], row, channel[col])
    col_mass = coop_mass_def4(matrix, zoo[col], col, channel[row])
    return (
        "C" if row_mass >= alpha - _MASS_TOL else "D",
        "C" if col_mass >= alpha - _MASS_TOL else "D",
    )


def compare_at(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot],
    bots: tuple[str, ...],
    t: float,
    alpha: float,
    channel: dict[str, Signal],
) -> Comparison:
    """Both matrices at one (t, α)."""
    cells = tuple(
        CellPair(
            row=row,
            col=col,
            def3=def3_actions(matrix, row, col, alpha, channel),
            def4=def4_actions(matrix, zoo, row, col, alpha, channel),
        )
        for row in bots
        for col in bots
    )
    return Comparison(t=t, alpha=alpha, cells=cells)


def alpha_breakpoints_both(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot],
    bots: tuple[str, ...],
    channel: dict[str, Signal],
    quantize: int = 9,
) -> list[float]:
    """The union of both definitions' achievable cooperation masses.

    Between two consecutive breakpoints every α gives identical behavior under
    BOTH definitions, so enumerating these makes the α axis exact rather than
    sampled. We take the union so neither definition's phase change is missed.
    """
    masses = {0.0}
    for actor in bots:
        for signal in channel.values():
            masses.add(round(coop_mass(matrix, actor, signal), quantize))
            masses.add(round(coop_mass_def4(matrix, zoo[actor], actor, signal), quantize))
    return sorted(masses)


def alpha_bands(breakpoints: list[float]) -> list[tuple[float, float, float]]:
    """Turn breakpoints into (probe_alpha, band_lo, band_hi) triples.

    Behavior is constant on `(prev, bp]` — the `≥ α` convention means a mass
    exactly at a breakpoint still cooperates — so we probe AT the breakpoint,
    which is the representative α of the band ending there. The band above the
    largest achievable mass (where every agent defects) is probed just past it.
    """
    bands: list[tuple[float, float, float]] = []
    prev = 0.0
    for bp in breakpoints:
        bands.append((bp, prev, bp))
        prev = bp
    top = breakpoints[-1] if breakpoints else 0.0
    if top < 1.0:
        bands.append(((top + 1.0) / 2, top, 1.0))
    return bands


@dataclass(frozen=True)
class Divergence:
    """A (t, α) region where the two definitions' matrices differ."""

    t: float
    alpha: float
    cells: tuple[CellPair, ...]


def sweep(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot] | None = None,
    bots: tuple[str, ...] = COMPARISON_BOTS,
    t_values: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
) -> tuple[list[Comparison], list[Divergence]]:
    """Compare both definitions across the (t, α) grid.

    The α axis is exact (breakpoint bands); `t_values` is sampled, since the
    transparency dial is continuous and its breakpoints are not finitely
    enumerable in the same clean way.
    """
    zoo = zoo or CONTROL_ZOO
    distances = behavioral_distance_matrix(matrix)
    comparisons: list[Comparison] = []
    divergences: list[Divergence] = []
    for t in t_values:
        channel = signal_family(matrix, t, distances=distances)
        breakpoints = alpha_breakpoints_both(matrix, zoo, bots, channel)
        for alpha, _lo, _hi in alpha_bands(breakpoints):
            comp = compare_at(matrix, zoo, bots, t, alpha, channel)
            comparisons.append(comp)
            if not comp.agrees:
                divergences.append(
                    Divergence(t=t, alpha=alpha, cells=comp.disagreements)
                )
    return comparisons, divergences


# ── Why a zoo does (or does not) separate the definitions ──────────────────


@dataclass(frozen=True)
class AsymmetryReport:
    """Whether the two definitions can differ AT ALL on this zoo.

    The decisive question is not "does the base matrix have asymmetric cells"
    but "does any bot's BIT-VECTOR differ between the two probe geometries".
    Those come apart: an asymmetric base cell whose actor is a CONSTANT bot
    changes nothing, because a constant's vector is all-ones or all-zeros under
    every probe. Only a differing bit-vector can move a cooperation mass, and
    only a moved mass can shift a phase boundary.

    So `can_separate` is decided by `bit_divergences`; `asymmetric_pairs` is
    reported alongside as the *diagnostic* that explains where a divergence
    could come from (self and reciprocity probes read the same cell from
    opposite sides, so they can only disagree on an asymmetric cell).
    """

    asymmetric_pairs: tuple[tuple[str, str, str, str], ...]
    """(actor, hypothesis, actor_action, hypothesis_action) for each asymmetry."""

    bit_divergences: tuple[tuple[str, str, bool, bool], ...]
    """(actor, hypothesis, def3_bit, def4_bit) wherever the probe bits differ."""

    bit_vectors: tuple[tuple[str, tuple[bool, ...], tuple[bool, ...]], ...]
    """(actor, def3_vector, def4_vector) — the full picture, for reporting."""

    @property
    def can_separate(self) -> bool:
        """True iff some bot's probe bits actually differ between definitions."""
        return bool(self.bit_divergences)


def asymmetry_report(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot] | None = None,
    bots: tuple[str, ...] = COMPARISON_BOTS,
) -> AsymmetryReport:
    """Decide whether Def 3 and Def 4 can differ on this zoo, and say why.

    Run this BEFORE reading an agreement result as meaningful: if
    `can_separate` is False, the two definitions are identical here at EVERY
    (t, α) — no sweep can show otherwise — and the experiment needs a
    hypothesis whose probe bits actually differ to become informative.
    """
    zoo = zoo or CONTROL_ZOO
    asym: list[tuple[str, str, str, str]] = []
    for actor in bots:
        for hyp in bots:
            a_act = matrix.action(actor, hyp)
            h_act = matrix.action(hyp, actor)
            if a_act != h_act:
                asym.append((actor, hyp, a_act, h_act))

    diverge: list[tuple[str, str, bool, bool]] = []
    vectors: list[tuple[str, tuple[bool, ...], tuple[bool, ...]]] = []
    for actor in bots:
        bot = zoo[actor]
        d3 = tuple(matrix.cooperates(actor, h) for h in bots)
        d4 = tuple(probe_bit(matrix, bot, actor, h) for h in bots)
        vectors.append((actor, d3, d4))
        for hyp, b3, b4 in zip(bots, d3, d4):
            if b3 != b4:
                diverge.append((actor, hyp, b3, b4))

    return AsymmetryReport(
        asymmetric_pairs=tuple(asym),
        bit_divergences=tuple(diverge),
        bit_vectors=tuple(vectors),
    )


# ── Rendering ──────────────────────────────────────────────────────────────


def _fmt_cell(pair: tuple[str, str]) -> str:
    return f"({pair[0]},{pair[1]})"


def render_side_by_side(
    comp: Comparison,
    bots: tuple[str, ...] = COMPARISON_BOTS,
    labels: dict[str, str] | None = None,
) -> str:
    """Two outcome matrices printed side by side, with disagreements marked."""
    labels = labels or {b: b.replace("Bot", "") for b in bots}
    m3 = comp.matrix("def3")
    m4 = comp.matrix("def4")
    width = max(9, max(len(labels[b]) for b in bots) + 1)
    head = " " * width + "".join(labels[b].rjust(width) for b in bots)
    sep = "   │   "

    lines = [
        f"t = {comp.t:.2f},  α = {comp.alpha:.4f}"
        + ("   [MATRICES AGREE]" if comp.agrees else "   [*** DIVERGE ***]"),
        "",
        "Def 3 (self probe)".ljust(len(head)) + sep + "Def 4 (tau-native probes)",
        head + sep + head,
    ]
    for row in bots:
        left = labels[row].ljust(width)
        right = labels[row].ljust(width)
        for col in bots:
            c3, c4 = m3[(row, col)], m4[(row, col)]
            mark = " " if c3 == c4 else "*"
            left += (_fmt_cell(c3) + mark).rjust(width)
            right += (_fmt_cell(c4) + mark).rjust(width)
        lines.append(left + sep + right)
    return "\n".join(lines)


def render_report(
    matrix: TauMatrix,
    zoo: dict[str, Def4Bot] | None = None,
    bots: tuple[str, ...] = COMPARISON_BOTS,
    t_values: tuple[float, ...] = (0.0, 0.25, 0.5, 0.75, 1.0),
) -> str:
    """The full comparison report: asymmetry analysis, then the (t, α) tables."""
    zoo = zoo or CONTROL_ZOO
    labels = {b: (zoo[b].name.replace("Tau", "τ") if b in zoo else b) for b in bots}
    report = asymmetry_report(matrix, zoo, bots)

    out: list[str] = [
        "═" * 100,
        "Def 3 vs Def 4 — side-by-side (t, α) outcome matrices",
        "═" * 100,
        "",
        "Zoo (base bot → tau bot, probe geometry):",
    ]
    for b in bots:
        bd = zoo[b]
        ref = f" vs {bd.referent}" if bd.referent else ""
        out.append(f"  {b:<16} → {bd.name:<14} [{bd.probe.value}{ref}]")

    out += [
        "",
        "Base outcome matrix (the certified cells both definitions read):",
        "  " + " " * 16 + "".join(b.replace("Bot", "").rjust(10) for b in bots),
    ]
    for row in bots:
        out.append(
            f"  {row:<16}"
            + "".join(
                _fmt_cell((matrix.action(row, col), matrix.action(col, row))).rjust(10)
                for col in bots
            )
        )

    out += ["", "─" * 100, "CAN THIS ZOO SEPARATE THE DEFINITIONS?", "─" * 100]
    out.append("Probe bit-vectors (hypothesis order: " + ", ".join(bots) + "):")
    for actor, d3, d4 in report.bit_vectors:
        v3 = "".join("1" if b else "0" for b in d3)
        v4 = "".join("1" if b else "0" for b in d4)
        mark = "" if d3 == d4 else "   <<< DIFFER"
        out.append(
            f"  {actor:<16} [{zoo[actor].probe.value:<12}] "
            f"Def3 {v3}   Def4 {v4}{mark}"
        )
    out.append("")
    if report.asymmetric_pairs:
        out.append("Asymmetric base cells (where self/reciprocity probes COULD differ):")
        for actor, hyp, a, h in report.asymmetric_pairs:
            out.append(f"  {actor} vs {hyp}: {actor} plays {a}, {hyp} plays {h}")
        out.append("")
    if report.bit_divergences:
        out.append("Probe bits that actually differ:")
        for actor, hyp, b3, b4 in report.bit_divergences:
            out.append(
                f"  {zoo[actor].name} on {hyp}: "
                f"Def3 {'C' if b3 else 'D'} → Def4 {'C' if b4 else 'D'}"
            )
        out += [
            "",
            "⇒ The definitions CAN diverge on this zoo; see the tables below for",
            "  the (t, α) regions where the shifted mass actually crosses a",
            "  threshold.",
        ]
    else:
        out += [
            "⇒ Every bot has the SAME bit-vector under both definitions, so the",
            "  two are PROVABLY IDENTICAL on this zoo at every (t, α) — no sweep",
            "  can show otherwise. The tables below are a control/anchor result,",
            "  NOT evidence that the choice of definition is immaterial in",
            "  general.",
        ]
        if report.asymmetric_pairs:
            out += [
                "",
                "  Note the asymmetric cells above did NOT separate them: their",
                "  actors are CONSTANT bots, whose bit-vector is all-ones or",
                "  all-zeros under every probe geometry. Asymmetry only bites",
                "  when it sits under a CONDITIONAL bot's probe.",
            ]
        out += [
            "",
            "  To make the comparison informative, add a hypothesis that a",
            "  conditional bot reads differently under self vs reciprocity —",
            "  i.e. an exploiter/exploited pair such as DupocBot vs EBot =",
            "  (D, C), where Dupoc defects but the hypothesis cooperates.",
        ]

    comparisons, divergences = sweep(matrix, zoo, bots, t_values)

    out += ["", "─" * 100, f"(t, α) TABLES  —  large k, {len(comparisons)} phase cells", "─" * 100]
    for comp in comparisons:
        out += ["", render_side_by_side(comp, bots, labels)]

    out += ["", "═" * 100, "SUMMARY", "═" * 100]
    out.append(f"Phase cells compared : {len(comparisons)}")
    out.append(f"Cells where matrices diverge : {len(divergences)}")
    if divergences:
        for d in divergences:
            out.append(f"  t = {d.t:.2f}, α = {d.alpha:.4f}:")
            for c in d.cells:
                out.append(
                    f"    {c.row} vs {c.col}: "
                    f"Def3 {_fmt_cell(c.def3)}  ≠  Def4 {_fmt_cell(c.def4)}"
                )
    else:
        out.append("  (none — see the separation analysis above for why)")
    out.append("")
    out.append("Caveat: all tables at LARGE k (past the Löb threshold), where the")
    out.append("Lean Def-4 phase theorems hold. The sub-Löb regime is unproven and")
    out.append("not modelled here.")
    return "\n".join(out)


def main() -> None:
    import argparse

    from pd_runner.tau.def4 import (
        CONTROL_BOTS,
        SEPARATING_BOTS,
        SEPARATING_ZOO,
    )
    from pd_runner.tau.matrix import load_tau_matrix

    parser = argparse.ArgumentParser(
        description="Compare Def-3 and Def-4 tau semantics side by side."
    )
    parser.add_argument(
        "--zoo",
        choices=("control", "separating"),
        default="control",
        help=(
            "control = the 4-bot milestone-1 zoo (provably identical under both "
            "definitions — the anchor run); separating = control + EBot, whose "
            "asymmetric cell under a conditional bot makes the definitions "
            "diverge (the informative run)"
        ),
    )
    parser.add_argument(
        "--t-values",
        default="0,0.25,0.5,0.75,1.0",
        help="comma-separated transparency values (default: 0,0.25,0.5,0.75,1.0)",
    )
    parser.add_argument(
        "--bots",
        default=None,
        help="override the zoo's bot list (comma-separated base bot names)",
    )
    parser.add_argument(
        "--summary-only",
        action="store_true",
        help="print the separation analysis and summary, skipping the tables",
    )
    args = parser.parse_args()

    zoo = CONTROL_ZOO if args.zoo == "control" else SEPARATING_ZOO
    default_bots = CONTROL_BOTS if args.zoo == "control" else SEPARATING_BOTS
    bots = (
        tuple(b.strip() for b in args.bots.split(","))
        if args.bots
        else default_bots
    )
    t_values = tuple(float(x) for x in args.t_values.split(","))
    matrix = load_tau_matrix(bots)
    text = render_report(matrix, zoo, bots, t_values)
    if args.summary_only:
        lines = text.split("\n")
        start = next(i for i, l in enumerate(lines) if "TABLES" in l)
        end = next(i for i, l in enumerate(lines) if l.strip() == "SUMMARY")
        text = "\n".join(lines[: start - 1] + lines[end - 1 :])
    print(text)


if __name__ == "__main__":
    main()

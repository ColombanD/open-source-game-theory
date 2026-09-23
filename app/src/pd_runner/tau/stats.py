"""Report STATISTICS — the numbers behind the tau report's charts.

Split out of `report.py` (2026-08-24), which had grown to ~1,570 lines by
mixing three concerns: computing the sweep numbers, rendering them as inline
SVG, and emitting the HTML shell. This module is the first of those, and it is
the half worth testing directly — every function here returns plain data
structures and touches no markup.

The dependency runs one way: `report` imports `stats`, never the reverse. The
chart-geometry constants (colours, band layouts, CSS) stay with the renderer;
the sampling grids live here because they define WHAT is computed, and
`report` re-exports them for its callers.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.signal import behavioral_distance_matrix
from pd_runner.tau.sweep import run_tournament

if TYPE_CHECKING:
    from pd_runner.tau.channels import SigmaFamily


# Transparency levels sampled left-to-right on the x-axis (1.0 = full).
_TRANSPARENCY_GRID = [round(1.0 - 0.025 * i, 3) for i in range(41)]
_DEFAULT_ALPHAS = (0.3, 0.45, 0.62, 0.8)

# The α slider's grid. The report is self-contained static HTML, so the slider
# works by pre-rendering the two single-α panels (composition, robustness
# thresholds) at every grid value and swapping them client-side — no server in
# the loop. 0.05 steps avoid the achievable-mass knife edges (k/11 fractions)
# everywhere except the harmless α = 1 endpoint, where the fsum/tolerance
# handling already keeps unanimous masses cooperating.
_SLIDER_ALPHAS = tuple(round(0.05 * i, 2) for i in range(1, 21))

# The transparency slider's grid — the SECOND cursor, driving the two views
# that are a point in the (t, α) plane rather than a curve over one of them
# (per-bot composition, per-bot α-deviation). Coarser than `_TRANSPARENCY_GRID`
# (0.1 steps, 11 values) because every value is a pre-rendered panel and these
# views multiply with the α grid: 20 α × 11 t × 3 families is already 660
# tournaments per view.
_SLIDER_TRANSPARENCIES = tuple(round(1.0 - 0.1 * i, 2) for i in range(11))

@dataclass(frozen=True)
class SweepPoint:
    target_transparency: float
    temperature: float
    actual_transparency: float
    mutual_coop_rate: float
    coop_rate: float
    degenerate: bool


def sweep_by_transparency(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float] | None = None,
    family: "SigmaFamily | None" = None,
) -> list[SweepPoint]:
    """One tournament per dial value; the dial IS the transparency target."""
    distances = behavioral_distance_matrix(matrix) if family is None else None
    points = []
    for target in targets if targets is not None else _TRANSPARENCY_GRID:
        result = run_tournament(matrix, target, alpha, distances, family=family)
        points.append(SweepPoint(
            target_transparency=target,
            temperature=result.temperature,
            actual_transparency=result.transparency,
            mutual_coop_rate=result.mutual_coop_rate,
            coop_rate=result.coop_rate,
            degenerate=result.is_degenerate,
        ))
    return points


def base_rows(matrix: TauMatrix) -> dict[str, tuple[str, ...]]:
    """Each bot's own action row in the BASE matrix — the t = 1 reference."""
    return {b: tuple(matrix.action(b, o) for o in matrix.bots) for b in matrix.bots}


def stable_bot_order(matrix: TauMatrix) -> tuple[str, ...]:
    """The row order EVERY per-bot chart uses, fixed across all cursor values.

    Sorted by base-matrix cooperativeness (most cooperative first), ties broken
    by name. Derived from the base matrix alone, so it depends on neither t, α
    nor the σ family.

    That independence is the whole point. Sorting each panel by its own values
    — by threshold, by peak deviation, by cooperation count — reads better in a
    single screenshot but destroys the comparison the cursors exist to support:
    a bot changes row as you drag, so you track a moving target and two panels
    at different cursor values cannot be read against each other. A fixed order
    means a bot's row is the same row everywhere, and the eye can follow one
    strip while the dial moves.
    """
    coop = {
        b: sum(1 for o in matrix.bots if matrix.cooperates(b, o)) for b in matrix.bots
    }
    return tuple(sorted(matrix.bots, key=lambda b: (-coop[b], b)))


def row_deviation(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float] | None = None,
    family: "SigmaFamily | None" = None,
) -> dict[str, list[tuple[float, float]]]:
    """Per-bot deviation profile: how much the tau row differs from the base row.

    The magnitude at each transparency is the normalized Hamming distance
    between the bot's tau-lifted action row and its base-matrix row — i.e. the
    fraction of opponents against which the lift changed the bot's mind. `0.0`
    means "still behaving as itself"; the threshold chart's bar is exactly the
    first x where this leaves 0.

    Deviation is graded on purpose: a bot that flips one cell of eleven and a
    bot that inverts its whole row both cross the same threshold, and the
    threshold chart alone cannot tell them apart.

    NOT MONOTONE in t, by construction rather than by accident. As t → 0 every
    signal converges to the same uniform mixture, so every opponent's
    cooperation mass converges to a single limit — the actor's own base
    cooperation fraction. Masses approaching that limit from opposite sides can
    cross α in opposite directions at nearby t, so the flipped-cell count can
    DECREASE as the signal degrades: a bot may depart from its base row and
    then return to it. Rare (it needs two cells crossing in opposite directions
    close together) and concentrated at the opaque end, but real — do not
    "clean up" a profile that dips, and do not treat the first departure as a
    permanent one.
    """
    distances = behavioral_distance_matrix(matrix) if family is None else None
    base = base_rows(matrix)
    n = len(matrix.bots)
    profile: dict[str, list[tuple[float, float]]] = {b: [] for b in matrix.bots}
    for target in targets if targets is not None else _TRANSPARENCY_GRID:
        result = run_tournament(matrix, target, alpha, distances, family=family)
        for bot in matrix.bots:
            row = tuple(result.cells[(bot, o)][0] for o in matrix.bots)
            flipped = sum(1 for a, b in zip(row, base[bot]) if a != b)
            profile[bot].append((target, flipped / n))
    return profile


def alpha_deviation(
    matrix: TauMatrix,
    target: float,
    alphas: tuple[float, ...] | list[float] = _SLIDER_ALPHAS,
    family: "SigmaFamily | None" = None,
) -> dict[str, list[tuple[float, float]]]:
    """The α-axis transpose of `row_deviation`: fixed transparency, α swept.

    Answers "at THIS much transparency, for which caution thresholds does each
    bot stop behaving like its base bot?" — the dial the robustness chart holds
    fixed. Same normalized-Hamming magnitude, so the two charts share a colour
    scale and can be read against each other.
    """
    distances = behavioral_distance_matrix(matrix) if family is None else None
    base = base_rows(matrix)
    n = len(matrix.bots)
    profile: dict[str, list[tuple[float, float]]] = {b: [] for b in matrix.bots}
    for alpha in alphas:
        result = run_tournament(matrix, target, alpha, distances, family=family)
        for bot in matrix.bots:
            row = tuple(result.cells[(bot, o)][0] for o in matrix.bots)
            flipped = sum(1 for a, b in zip(row, base[bot]) if a != b)
            profile[bot].append((alpha, flipped / n))
    return profile


def per_bot_composition(
    matrix: TauMatrix,
    alpha: float,
    target: float,
    family: "SigmaFamily | None" = None,
) -> dict[str, dict[str, int]]:
    """Per-bot outcome counts over its own row: (C,C) / (C,D) / (D,C) / (D,D).

    Read from the ROW bot's seat, so the first letter is always what this bot
    played: `CD` is "I cooperated, they defected" (I was exploited) and `DC` is
    "I defected, they cooperated" (I exploited). Chart 3's aggregate pools the
    two exploitation directions; per bot they are opposite facts about the same
    bot and must not be pooled.
    """
    distances = behavioral_distance_matrix(matrix) if family is None else None
    result = run_tournament(matrix, target, alpha, distances, family=family)
    counts: dict[str, dict[str, int]] = {
        b: {"CC": 0, "DC": 0, "CD": 0, "DD": 0, "other": 0} for b in matrix.bots
    }
    for bot in matrix.bots:
        for opp in matrix.bots:
            mine, theirs = result.cells[(bot, opp)]
            key = f"{mine}{theirs}"
            counts[bot][key if key in counts[bot] else "other"] += 1
    return counts


def robustness_thresholds(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float] | None = None,
    family: "SigmaFamily | None" = None,
) -> dict[str, float | None]:
    """Transparency at which each bot FIRST departs from its base-matrix row.

    `None` means the bot never deviates — its behavior is blur-proof at this α
    (true of the constant bots, which have no conditionality to lose).

    First is not permanent. Deviation is not monotone in t (see
    `row_deviation`), so a bot may return to its base row at some lower
    transparency; this number cannot express that, and callers that present it
    as "the transparency this bot needs" are overclaiming. Pair it with
    `row_deviation` — the report marks the returning rows with `°`.
    """
    distances = behavioral_distance_matrix(matrix) if family is None else None
    base = base_rows(matrix)
    thresholds: dict[str, float | None] = dict.fromkeys(matrix.bots)
    for target in targets if targets is not None else _TRANSPARENCY_GRID:
        result = run_tournament(matrix, target, alpha, distances, family=family)
        for bot in matrix.bots:
            if thresholds[bot] is None:
                row = tuple(result.cells[(bot, o)][0] for o in matrix.bots)
                if row != base[bot]:
                    thresholds[bot] = target
    return thresholds

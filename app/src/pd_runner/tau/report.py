"""Visual report for the tau layer — a self-contained HTML page.

Deliberately dependency-free: the charts are hand-rolled inline SVG, so the
report runs with no matplotlib/plotly in the environment and the output is a
single file that opens anywhere.

    uv run python -m pd_runner.tau.report
    uv run python -m pd_runner.tau.report --output ~/tau.html --open

Eight views, in the order the argument runs, controlled by three client-side
selectors — the α slider, the transparency (t) slider and the σ-family radio
(all views pre-rendered and swapped by ~30 lines of inline JS, since the page
must stay self-contained):

1. **Cooperation vs transparency** — the headline, one line per α, one view
   per σ family. The x-axis is the TRANSPARENCY dial (normalized MI), not a
   raw knob, because knobs are unitless and family-specific.
2. **Channel comparison at matched transparency** — one line per σ family at
   the selected α. The matched-MI money plot: at equal x, the information
   RATE is identical and only the confusion STRUCTURE differs, so the gap
   between the curves is the value of reading source over watching play.
3. **What cooperation displaces** — the (C,C)/exploitation/(D,D) composition.
3b. **Outcome mix per bot** — the same tournament broken out by bot, keeping
   (D,C) and (C,D) apart (who exploited whom, not just "exploitation").
4. **Robustness thresholds** — the transparency at which each bot first
   departs from its base-matrix row, the bar shaded by HOW MUCH of the row has
   changed there.
4b. **Caution tolerance per bot** — chart 4 transposed onto the α axis with t
   as the cursor; same deviation colour scale, so the two read together.
5. **(t, α) phase diagram** — the two dials crossed.
6. **The outcome matrix itself** — what everything above is computed from,
   with stipulated cells marked.
"""

from __future__ import annotations

import html
import json
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

from pd_runner.tau.matrix import DEFAULT_ZOO, ZOOS, NamedZoo, TauMatrix, get_zoo
from pd_runner.tau.signal import (
    behavioral_distance_matrix,
    behavioral_twins,
)
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

# Colour-blind-safe qualitative colours (Okabe–Ito).
_SERIES_COLORS = ("#0072b2", "#d55e00", "#009e73", "#cc79a7", "#e69f00")

# One fixed colour per σ family (chart 2 legend + consistency across views).
_FAMILY_COLORS = {"behavioral": "#0072b2", "epsilon": "#8c8c96", "syntactic": "#d55e00"}


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


# --------------------------------------------------------------- rendering ---

def _line_chart(
    series: list[tuple[str, list[tuple[float, float]], str]],
    width: int = 720,
    height: int = 320,
    y_label: str = "",
    value_format: str = "percent",
) -> str:
    """Inline SVG line chart. `series` = [(label, [(x, y)…], colour)].

    Carries a hover cursor: the series data is emitted as JSON on the `<svg>`
    so the shared `_CURSOR_SCRIPT` can snap a vertical rule to the nearest
    sampled transparency and read every series off at that x.
    """
    pad_l, pad_r, pad_t, pad_b = 56, 130, 16, 44
    plot_w, plot_h = width - pad_l - pad_r, height - pad_t - pad_b

    # x runs 1.0 (full transparency) on the LEFT down to 0.0 on the right, so
    # the reader moves left-to-right in the direction of degrading signal.
    def sx(x: float) -> float:
        return pad_l + (1.0 - x) * plot_w

    def sy(y: float) -> float:
        return pad_t + (1.0 - y) * plot_h

    cursor_data = json.dumps({
        "padL": pad_l, "padT": pad_t, "plotW": plot_w, "plotH": plot_h,
        "format": value_format,
        "series": [
            {"label": label, "colour": colour,
             "points": [[round(x, 6), round(y, 6)] for x, y in points]}
            for label, points, colour in series
        ],
    }, separators=(",", ":"))

    parts = [
        f'<svg viewBox="0 0 {width} {height}" class="chart cursor-chart" '
        f"role=\"img\" data-cursor='{html.escape(cursor_data, quote=True)}'>"
    ]

    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        y = sy(frac)
        parts.append(
            f'<line x1="{pad_l}" y1="{y:.1f}" x2="{pad_l + plot_w}" y2="{y:.1f}" '
            f'class="grid"/>'
            f'<text x="{pad_l - 8}" y="{y + 4:.1f}" class="tick end">{frac:.0%}</text>'
        )
    for frac in (1.0, 0.75, 0.5, 0.25, 0.0):
        x = sx(frac)
        parts.append(
            f'<line x1="{x:.1f}" y1="{pad_t}" x2="{x:.1f}" y2="{pad_t + plot_h}" '
            f'class="grid"/>'
            f'<text x="{x:.1f}" y="{pad_t + plot_h + 20}" class="tick mid">{frac:.0%}</text>'
        )

    parts.append(
        f'<text x="{pad_l + plot_w / 2:.1f}" y="{height - 6}" class="axis mid">'
        f'transparency  (normalized mutual information) →  opaque</text>'
    )
    if y_label:
        cy = pad_t + plot_h / 2
        parts.append(
            f'<text x="14" y="{cy:.1f}" class="axis mid" '
            f'transform="rotate(-90 14 {cy:.1f})">{html.escape(y_label)}</text>'
        )

    for idx, (label, points, colour) in enumerate(series):
        path = " ".join(
            f"{'M' if i == 0 else 'L'}{sx(x):.1f},{sy(y):.1f}"
            for i, (x, y) in enumerate(points)
        )
        parts.append(f'<path d="{path}" class="line" stroke="{colour}"/>')
        ly = pad_t + 16 + idx * 20
        parts.append(
            f'<line x1="{pad_l + plot_w + 16}" y1="{ly}" '
            f'x2="{pad_l + plot_w + 38}" y2="{ly}" class="line" stroke="{colour}"/>'
            f'<text x="{pad_l + plot_w + 44}" y="{ly + 4}" class="legend">'
            f'{html.escape(label)}</text>'
        )

    parts.append(_cursor_overlay(len(series), pad_l, pad_t, plot_w, plot_h))
    parts.append("</svg>")
    return "".join(parts)


def _cursor_overlay(
    n_series: int,
    pad_l: float,
    pad_t: float,
    plot_w: float,
    plot_h: float,
) -> str:
    """The hover furniture: rule, per-series dots, readout box, hit area.

    Emitted hidden; `_CURSOR_SCRIPT` positions and reveals it on pointer move.
    The hit rectangle is last so it sits above the plotted paths and receives
    the events regardless of what it covers.
    """
    dots = "".join(
        f'<circle class="cursor-dot" data-i="{i}" r="3.5" cx="0" cy="0" '
        f'visibility="hidden"/>'
        for i in range(n_series)
    )
    rows = "".join(
        f'<text class="cursor-row" data-i="{i}" x="0" y="0" '
        f'visibility="hidden"></text>'
        for i in range(n_series)
    )
    return (
        f'<g class="cursor-layer" visibility="hidden">'
        f'<line class="cursor-rule" x1="0" y1="{pad_t}" x2="0" '
        f'y2="{pad_t + plot_h}"/>'
        f"{dots}"
        f'<rect class="cursor-box" x="0" y="0" width="0" height="0" rx="4"/>'
        f'<text class="cursor-head" x="0" y="0"></text>'
        f"{rows}"
        f"</g>"
        f'<rect class="cursor-hit" x="{pad_l}" y="{pad_t}" '
        f'width="{plot_w}" height="{plot_h}" fill="transparent"/>'
    )


# Deviation colour ramp, shared by charts 4 and 5 so the two are comparable at
# a glance. 0 = "behaves exactly like its base bot" is deliberately rendered as
# near-background rather than as a pale tint of the deviation hue: the eye
# should read "no cell present" for no deviation, and every visible warmth as a
# real behavioral change.
_DEVIATION_ZERO = "#e8e8ec"
_DEVIATION_RAMP = (
    (0.0, (232, 232, 236)),   # unchanged
    (0.25, (247, 213, 160)),  # a cell or two flipped
    (0.5, (232, 150, 60)),
    (0.75, (206, 84, 30)),
    (1.0, (140, 30, 22)),     # every cell in the row flipped
)


def _deviation_colour(value: float) -> str:
    """Interpolate the deviation ramp — pale grey (unchanged) → deep red."""
    v = min(max(value, 0.0), 1.0)
    for (lo, c_lo), (hi, c_hi) in zip(_DEVIATION_RAMP, _DEVIATION_RAMP[1:]):
        if v <= hi:
            span = hi - lo
            f = 0.0 if span <= 0 else (v - lo) / span
            r, g, b = (round(a + (b_ - a) * f) for a, b_ in zip(c_lo, c_hi))
            return f"#{r:02x}{g:02x}{b:02x}"
    return _DEVIATION_ZERO


def _deviation_legend(x: float, y: float, width: float = 150) -> str:
    """A small horizontal colour key for the deviation ramp."""
    steps = 24
    swatches = "".join(
        f'<rect x="{x + i * width / steps:.1f}" y="{y:.1f}" '
        f'width="{width / steps + 0.6:.1f}" height="9" '
        f'fill="{_deviation_colour(i / (steps - 1))}"/>'
        for i in range(steps)
    )
    return (
        f"{swatches}"
        f'<text x="{x:.1f}" y="{y + 22:.1f}" class="tick">same</text>'
        f'<text x="{x + width:.1f}" y="{y + 22:.1f}" class="tick end">row inverted</text>'
    )


def _threshold_chart(
    thresholds: dict[str, float | None],
    deviation: dict[str, list[tuple[float, float]]] | None = None,
    width: int = 720,
) -> str:
    """Horizontal bars: how much transparency each bot needs to behave as itself.

    When `deviation` is supplied the row becomes a full-width GRADIENT STRIP
    spanning the whole transparency axis, shaded at each sample by how much of
    the bot's row has changed there. The threshold is drawn as a tick on that
    strip rather than as the length of a bar.

    That is deliberate: deviation grows as transparency FALLS, so the
    informative region is to the RIGHT of the threshold (the blurrier side).
    Colouring only the bar — the span from full transparency down to the
    threshold — paints exactly the region where nothing has happened yet, which
    is uniformly "unchanged" by construction and says nothing. The strip shows
    the drift the threshold alone cannot express: a one-cell flip and a full
    row inversion cross at the same place but end up very differently.

    **Deviation is NOT monotone in t, and the threshold is only the FIRST
    departure.** A bot can leave its base row and later return to it as the
    signal degrades further: as t → 0 every signal converges to the same
    uniform mixture, so every opponent's cooperation mass converges to one
    shared limit (the bot's own base cooperation fraction). Masses approach
    that limit from opposite sides, so two cells can flip in opposite
    directions near the same t and the deviation COUNT dips. Rows where this
    happens are marked with a ° after the threshold — for those, "needs this
    much transparency" is true of the first departure only, and the strip, not
    the tick, is the honest summary.
    """
    ordered = sorted(
        thresholds.items(),
        key=lambda kv: (kv[1] is None, -(kv[1] or 0.0)),
    )
    row_h, pad_l, pad_r, pad_t = 26, 130, 60, 12
    legend_h = 34 if deviation else 0
    # 28 for the tick row + 16 for the axis title beneath it.
    height = pad_t + row_h * len(ordered) + 44 + legend_h
    plot_w = width - pad_l - pad_r
    grid_bottom = pad_t + row_h * len(ordered)

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    # x maps transparency 1.0 (full) to the LEFT edge and 0.0 (opaque) to the
    # right, like every other chart on the page — the reader always moves
    # left-to-right in the direction of degrading signal. The axis labels must
    # be placed through the SAME map as the strip segments and the threshold
    # tick, or the numbers under the chart mirror the marks on it.
    for frac in (1.0, 0.75, 0.5, 0.25, 0.0):
        x = pad_l + (1.0 - frac) * plot_w
        parts.append(
            f'<line x1="{x:.1f}" y1="{pad_t}" x2="{x:.1f}" '
            f'y2="{grid_bottom}" class="grid"/>'
            f'<text x="{x:.1f}" y="{grid_bottom + 20}" class="tick mid">{frac:.0%}</text>'
        )
    parts.append(
        f'<text x="{pad_l + plot_w / 2:.1f}" y="{grid_bottom + 20}" '
        f'class="axis mid" dy="16">transparency →  opaque</text>'
    )

    for i, (bot, value) in enumerate(ordered):
        y = pad_t + i * row_h
        parts.append(
            f'<text x="{pad_l - 10}" y="{y + 17}" class="tick end">{html.escape(bot)}</text>'
        )
        if value is None:
            if deviation is not None:
                # Draw the (uniformly unchanged) strip anyway, so the row is
                # visually comparable instead of blank, then label it.
                parts.append(
                    f'<rect x="{pad_l}" y="{y + 5}" width="{plot_w:.1f}" '
                    f'height="{row_h - 12}" fill="{_deviation_colour(0.0)}">'
                    f"<title>{html.escape(bot)}: identical to its base row at "
                    f"every transparency</title></rect>"
                )
            parts.append(
                f'<text x="{pad_l + 6}" y="{y + 17}" class="never">'
                f'never deviates (unconditional)</text>'
            )
            continue

        if deviation is None:
            parts.append(
                f'<rect x="{pad_l}" y="{y + 5}" width="{value * plot_w:.1f}" '
                f'height="{row_h - 12}" rx="3" fill="#0072b2" opacity="0.75"/>'
            )
            parts.append(
                f'<text x="{pad_l + value * plot_w + 8:.1f}" y="{y + 17}" '
                f'class="tick">{value:.0%}</text>'
            )
            continue

        # Samples run 1.0 → 0.0 (full → opaque), so x maps 1 - t exactly like
        # the grid. The strip spans the WHOLE axis: the interesting shading is
        # right of the threshold, where the bot has actually started drifting.
        samples = sorted(deviation.get(bot, []), key=lambda p: -p[0])
        for j, (t, dev) in enumerate(samples):
            x0 = pad_l + (1.0 - t) * plot_w
            if j + 1 < len(samples):
                x1 = pad_l + (1.0 - samples[j + 1][0]) * plot_w
            else:
                x1 = pad_l + plot_w
            parts.append(
                f'<rect x="{x0:.1f}" y="{y + 5}" width="{max(x1 - x0, 1.0):.1f}" '
                f'height="{row_h - 12}" fill="{_deviation_colour(dev)}">'
                f"<title>{html.escape(bot)} at transparency {t:.0%}: "
                f"{dev:.0%} of its row differs from the base matrix</title>"
                f"</rect>"
            )
        # The threshold: where the strip stops being grey. Marked rather than
        # measured by bar length, so length is never read as magnitude.
        #
        # `°` flags a row that RETURNS to its base behavior at some lower
        # transparency, so the tick is the first departure and not a permanent
        # one. Without it the tick silently claims monotonicity the deviation
        # does not have.
        returns = any(d == 0.0 for t, d in samples if t <= value + 1e-9)
        tx = pad_l + (1.0 - value) * plot_w
        note = (
            f"{html.escape(bot)}: first departs at {value:.0%} transparency"
            + (
                " — but returns to its base row at lower transparency, so this "
                "is not a permanent departure"
                if returns
                else ""
            )
        )
        parts.append(
            f'<line x1="{tx:.1f}" y1="{y + 2}" x2="{tx:.1f}" y2="{y + row_h - 7}" '
            f'stroke="#1a1a1a" stroke-width="1.6"><title>{note}</title></line>'
            f'<text x="{tx - 5:.1f}" y="{y + 17}" class="tick end">'
            f'{value:.0%}{"°" if returns else ""}<title>{note}</title></text>'
        )

    if deviation:
        parts.append(_deviation_legend(pad_l, grid_bottom + 46, 150))
    parts.append("</svg>")
    return "".join(parts)


def _alpha_deviation_chart(
    profile: dict[str, list[tuple[float, float]]],
    width: int = 720,
) -> str:
    """One row per bot; one cell per α, shaded by how far the row has drifted.

    The α-axis companion to chart 4. Where that chart fixes α and sweeps
    transparency, this fixes transparency (the cursor) and sweeps the agents'
    own caution, so the two together cover the (t, α) plane one bot-row at a
    time — the thing chart 5's aggregate heatmap necessarily averages away.
    """
    bots = sorted(
        profile,
        key=lambda b: (
            # Most-affected first: bots that never move sink to the bottom.
            -max((d for _, d in profile[b]), default=0.0),
            b,
        ),
    )
    alphas = [a for a, _ in profile[bots[0]]] if bots else []
    row_h, pad_l, pad_r, pad_t = 24, 130, 30, 26
    height = pad_t + row_h * len(bots) + 30 + 30
    plot_w = width - pad_l - pad_r
    cell_w = plot_w / max(len(alphas), 1)

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    parts.append(
        f'<text x="{pad_l + plot_w / 2:.1f}" y="14" class="axis mid">'
        f"caution threshold α →</text>"
    )

    for i, bot in enumerate(bots):
        y = pad_t + i * row_h
        parts.append(
            f'<text x="{pad_l - 10}" y="{y + 16}" class="tick end">'
            f"{html.escape(bot)}</text>"
        )
        for j, (alpha, dev) in enumerate(profile[bot]):
            parts.append(
                f'<rect x="{pad_l + j * cell_w:.1f}" y="{y + 3}" '
                f'width="{cell_w + 0.6:.1f}" height="{row_h - 6}" '
                f'fill="{_deviation_colour(dev)}">'
                f"<title>{html.escape(bot)} at α = {alpha:g}: "
                f"{dev:.0%} of its row differs from the base matrix</title>"
                f"</rect>"
            )

    grid_bottom = pad_t + row_h * len(bots)
    for j, alpha in enumerate(alphas):
        if j % max(1, len(alphas) // 10) == 0:
            parts.append(
                f'<text x="{pad_l + (j + 0.5) * cell_w:.1f}" y="{grid_bottom + 16}" '
                f'class="tick mid">{alpha:g}</text>'
            )
    parts.append(_deviation_legend(pad_l, grid_bottom + 30, 150))
    parts.append("</svg>")
    return "".join(parts)


_PER_BOT_BANDS = (
    ("CC", "#0072b2", "(C,C) mutual cooperation"),
    ("DC", "#e69f00", "(D,C) I exploited them"),
    ("CD", "#cc79a7", "(C,D) I was exploited"),
    ("DD", "#8c8c96", "(D,D) mutual defection"),
    ("other", "#5c5c66", "no outcome (N)"),
)


def _per_bot_composition_chart(
    counts: dict[str, dict[str, int]],
    width: int = 720,
) -> str:
    """Stacked bar per bot: its own row split into the four outcome pairs.

    Chart 3 aggregates over the whole tournament, which cannot say WHO is doing
    the cooperating. Here the first letter is always the row bot's own action,
    so (D,C) and (C,D) are kept apart — pooling them as "exploitation" would
    merge the exploiter with the exploited.
    """
    total = max((sum(c.values()) for c in counts.values()), default=1) or 1
    # Most-cooperative first: the ordering is the point of the chart.
    bots = sorted(counts, key=lambda b: (-counts[b]["CC"] - counts[b]["CD"], b))

    row_h, pad_l, pad_r, pad_t = 24, 130, 200, 16
    height = pad_t + row_h * len(bots) + 34
    plot_w = width - pad_l - pad_r

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    for i, bot in enumerate(bots):
        y = pad_t + i * row_h
        parts.append(
            f'<text x="{pad_l - 10}" y="{y + 16}" class="tick end">'
            f"{html.escape(bot)}</text>"
        )
        x = float(pad_l)
        for key, colour, label in _PER_BOT_BANDS:
            n = counts[bot].get(key, 0)
            if not n:
                continue
            seg = n / total * plot_w
            parts.append(
                f'<rect x="{x:.1f}" y="{y + 3}" width="{seg:.1f}" '
                f'height="{row_h - 6}" fill="{colour}" opacity="0.9">'
                f"<title>{html.escape(bot)}: {n} of {total} opponents — "
                f"{html.escape(label)}</title></rect>"
            )
            # Only label a segment wide enough to hold the count legibly.
            if seg >= 16:
                parts.append(
                    f'<text x="{x + seg / 2:.1f}" y="{y + 16}" class="tick mid" '
                    f'fill="#fff">{n}</text>'
                )
            x += seg

    grid_bottom = pad_t + row_h * len(bots)
    parts.append(
        f'<text x="{pad_l + plot_w / 2:.1f}" y="{grid_bottom + 20}" class="axis mid">'
        f"opponents in the zoo ({total} per bot) →</text>"
    )
    for idx, (_, colour, label) in enumerate(_PER_BOT_BANDS):
        ly = pad_t + 12 + idx * 18
        parts.append(
            f'<rect x="{pad_l + plot_w + 16}" y="{ly - 8}" width="14" height="11" '
            f'fill="{colour}" opacity="0.9"/>'
            f'<text x="{pad_l + plot_w + 36}" y="{ly + 2}" class="legend">'
            f"{html.escape(label)}</text>"
        )
    parts.append("</svg>")
    return "".join(parts)


# Hover cursor shared by every x-axis chart. Plain string (not an f-string):
# JS braces stay literal. Snaps to the nearest SAMPLED x rather than
# interpolating, so the readout always shows a value that was actually
# computed — an interpolated number would invite reading a tournament that was
# never run.
_CURSOR_SCRIPT = """<script>(function () {
  var FMT = {
    percent: function (v) { return (v * 100).toFixed(1) + "%"; },
    number: function (v) { return v.toFixed(2); }
  };
  document.querySelectorAll("svg.cursor-chart").forEach(function (svg) {
    var cfg;
    try { cfg = JSON.parse(svg.dataset.cursor); } catch (e) { return; }
    if (!cfg.series.length || !cfg.series[0].points.length) return;
    var fmt = FMT[cfg.format] || FMT.number;
    var layer = svg.querySelector(".cursor-layer");
    var rule = svg.querySelector(".cursor-rule");
    var box = svg.querySelector(".cursor-box");
    var head = svg.querySelector(".cursor-head");
    var dots = svg.querySelectorAll(".cursor-dot");
    var rows = svg.querySelectorAll(".cursor-row");
    var hit = svg.querySelector(".cursor-hit");
    var xs = cfg.series[0].points.map(function (p) { return p[0]; });

    function sx(x) { return cfg.padL + (1 - x) * cfg.plotW; }
    function sy(y) { return cfg.padT + (1 - y) * cfg.plotH; }

    function move(evt) {
      // Map client px -> viewBox units; the SVG scales with the page width.
      var rect = svg.getBoundingClientRect();
      var vb = svg.viewBox.baseVal;
      var px = (evt.clientX - rect.left) / rect.width * vb.width;
      var target = 1 - (px - cfg.padL) / cfg.plotW;
      var best = 0;
      for (var i = 1; i < xs.length; i++) {
        if (Math.abs(xs[i] - target) < Math.abs(xs[best] - target)) best = i;
      }
      var x = xs[best];
      var cx = sx(x);
      rule.setAttribute("x1", cx); rule.setAttribute("x2", cx);
      head.textContent = "t = " + (x * 100).toFixed(0) + "%";

      // Longest row decides the box width (no text metrics in plain SVG).
      var longest = head.textContent.length;
      cfg.series.forEach(function (s, i) {
        var v = s.points[best][1];
        var text = s.label + "  " + fmt(v);
        if (text.length > longest) longest = text.length;
        rows[i].textContent = text;
        rows[i].setAttribute("fill", s.colour);
        dots[i].setAttribute("cx", cx);
        dots[i].setAttribute("cy", sy(v));
        dots[i].setAttribute("fill", s.colour);
        dots[i].setAttribute("visibility", "visible");
      });

      var bw = longest * 6.2 + 16, bh = 20 + cfg.series.length * 15;
      // Flip the box to the left of the rule when it would overflow.
      var bx = cx + 12;
      if (bx + bw > cfg.padL + cfg.plotW) bx = cx - 12 - bw;
      var by = cfg.padT + 6;
      box.setAttribute("x", bx); box.setAttribute("y", by);
      box.setAttribute("width", bw); box.setAttribute("height", bh);
      head.setAttribute("x", bx + 8); head.setAttribute("y", by + 15);
      rows.forEach(function (r, i) {
        r.setAttribute("x", bx + 8);
        r.setAttribute("y", by + 30 + i * 15);
        r.setAttribute("visibility", "visible");
      });
      layer.setAttribute("visibility", "visible");
    }

    hit.addEventListener("mousemove", move);
    hit.addEventListener("mouseleave", function () {
      layer.setAttribute("visibility", "hidden");
    });
  });
})();</script>"""


_COMPOSITION_BANDS = (
    ("CC", "#0072b2", "mutual cooperation (C,C)"),
    ("exploit", "#e69f00", "exploitation (C,D) + (D,C)"),
    ("DD", "#8c8c96", "mutual defection (D,D)"),
)

# Rendered width of the word "degenerate" at the 11px `.tick` size, rounded up.
# SVG has no text metrics at build time, so the wrap decision uses this
# estimate rather than measuring.
_DEGENERATE_LABEL_W = 62


def _composition_chart(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float],
    width: int = 720,
    height: int = 300,
    family: "SigmaFamily | None" = None,
) -> str:
    """Stacked bands showing what the non-cooperative cells actually are.

    The headline rate only counts (C,C). Splitting out exploitation and mutual
    defection reveals WHICH outcome cooperation is displacing as blur rises —
    the difference between real cooperation and bots being fooled.
    """
    distances = behavioral_distance_matrix(matrix) if family is None else None
    pad_l, pad_r, pad_t, pad_b = 56, 200, 16, 44
    plot_w, plot_h = width - pad_l - pad_r, height - pad_t - pad_b

    def sx(x: float) -> float:
        return pad_l + (1.0 - x) * plot_w

    def sy(y: float) -> float:
        return pad_t + (1.0 - y) * plot_h

    samples = []
    for target in targets:
        result = run_tournament(matrix, target, alpha, distances, family=family)
        samples.append((target, result.composition, result.is_degenerate))

    # Cursor reads the BAND values (not the stacked tops), which is what a
    # reader wants: "at 40% transparency, how much is exploitation?".
    cursor_data = json.dumps({
        "padL": pad_l, "padT": pad_t, "plotW": plot_w, "plotH": plot_h,
        "format": "percent",
        "series": [
            {"label": label, "colour": colour,
             "points": [[round(t, 6), round(comp[key], 6)]
                        for t, comp, _ in samples]}
            for key, colour, label in _COMPOSITION_BANDS
        ],
    }, separators=(",", ":"))

    parts = [
        f'<svg viewBox="0 0 {width} {height}" class="chart cursor-chart" '
        f"role=\"img\" data-cursor='{html.escape(cursor_data, quote=True)}'>"
    ]

    # Stack the bands bottom-up: CC, then exploitation, then DD fills to 1.0.
    floor = [0.0] * len(samples)
    for key, colour, label in _COMPOSITION_BANDS:
        top = [floor[i] + comp[key] for i, (_, comp, _) in enumerate(samples)]
        upper = " ".join(
            f"{'M' if i == 0 else 'L'}{sx(t):.1f},{sy(v):.1f}"
            for i, ((t, _, _), v) in enumerate(zip(samples, top))
        )
        lower = " ".join(
            f"L{sx(t):.1f},{sy(v):.1f}"
            for (t, _, _), v in zip(reversed(samples), reversed(floor))
        )
        parts.append(f'<path d="{upper} {lower} Z" fill="{colour}" opacity="0.85"/>')
        floor = top

    # Degenerate region: where every bot plays unconditionally, the numbers are
    # the classical-PD limit rather than a transparency effect.
    degenerate = [t for t, _, deg in samples if deg]
    if degenerate:
        edge = sx(max(degenerate))
        band = pad_l + plot_w - edge
        parts.append(
            f'<rect x="{edge:.1f}" y="{pad_t}" '
            f'width="{band:.1f}" height="{plot_h}" '
            f'fill="none" stroke="#d55e00" stroke-width="1.5" '
            f'stroke-dasharray="4 3"/>'
        )
        # The label must stay INSIDE the plot: the degenerate band is usually
        # narrow (it can even be zero-width, at the last sample only), and a
        # left-anchored label drawn rightward would run past the plot edge and
        # collide with the legend column. Right-anchor it to the plot edge when
        # the band is too narrow to hold it.
        if band >= _DEGENERATE_LABEL_W + 8:
            parts.append(
                f'<text x="{edge + 6:.1f}" y="{pad_t + 14}" '
                f'class="tick" fill="#d55e00">degenerate</text>'
            )
        else:
            parts.append(
                f'<text x="{pad_l + plot_w - 4:.1f}" y="{pad_t + 14}" '
                f'class="tick end" fill="#d55e00">degenerate</text>'
            )

    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        parts.append(
            f'<text x="{pad_l - 8}" y="{sy(frac) + 4:.1f}" class="tick end">'
            f'{frac:.0%}</text>'
        )
    for frac in (1.0, 0.75, 0.5, 0.25, 0.0):
        parts.append(
            f'<text x="{sx(frac):.1f}" y="{pad_t + plot_h + 20}" class="tick mid">'
            f'{frac:.0%}</text>'
        )
    parts.append(
        f'<text x="{pad_l + plot_w / 2:.1f}" y="{height - 6}" class="axis mid">'
        f'transparency →  opaque</text>'
    )
    for idx, (_, colour, label) in enumerate(_COMPOSITION_BANDS):
        ly = pad_t + 16 + idx * 20
        parts.append(
            f'<rect x="{pad_l + plot_w + 16}" y="{ly - 8}" width="14" height="11" '
            f'fill="{colour}" opacity="0.85"/>'
            f'<text x="{pad_l + plot_w + 36}" y="{ly + 2}" class="legend">'
            f'{html.escape(label)}</text>'
        )

    parts.append(
        _cursor_overlay(len(_COMPOSITION_BANDS), pad_l, pad_t, plot_w, plot_h)
    )
    parts.append("</svg>")
    return "".join(parts)


def _phase_diagram(
    matrix: TauMatrix,
    alphas: list[float],
    targets: list[float],
    width: int = 720,
    family: "SigmaFamily | None" = None,
) -> str:
    """Heatmap of mutual cooperation over the (transparency, α) grid."""
    distances = behavioral_distance_matrix(matrix) if family is None else None
    cell_w = (width - 150) / len(targets)
    cell_h = 30
    height = 40 + cell_h * len(alphas) + 34

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    for r, alpha in enumerate(alphas):
        y = 24 + r * cell_h
        parts.append(
            f'<text x="104" y="{y + cell_h / 2 + 4:.1f}" class="tick end">'
            f'α = {alpha:g}</text>'
        )
        for c, target in enumerate(targets):
            rate = run_tournament(
                matrix, target, alpha, distances, family=family
            ).mutual_coop_rate
            # Single-hue ramp: pale = defection, saturated blue = cooperation.
            shade = 0.12 + 0.88 * rate
            parts.append(
                f'<rect x="{114 + c * cell_w:.1f}" y="{y}" '
                f'width="{cell_w + 0.6:.1f}" height="{cell_h}" '
                f'fill="#0072b2" opacity="{shade:.3f}">'
                f'<title>transparency {target:.0%}, α={alpha:g}: '
                f'mutual cooperation {rate:.0%}</title></rect>'
            )
    for c, target in enumerate(targets):
        if c % max(1, len(targets) // 8) == 0:
            parts.append(
                f'<text x="{114 + c * cell_w:.1f}" y="{height - 12}" '
                f'class="tick mid">{target:.0%}</text>'
            )
    parts.append(
        f'<text x="{width / 2:.1f}" y="16" class="axis mid">'
        f'transparency →  opaque   (cell shade = mutual cooperation rate)</text>'
    )
    parts.append("</svg>")
    return "".join(parts)


def _matrix_table(matrix: TauMatrix) -> str:
    head = "".join(f"<th>{html.escape(b[:6])}</th>" for b in matrix.bots)
    rows = []
    for row_bot in matrix.bots:
        cells = []
        for col_bot in matrix.bots:
            cell = matrix.cell(row_bot, col_bot)
            classes = [{"C": "c", "N": "n"}.get(cell.row_action, "d")]
            if cell.hypothetical:
                classes.append("hyp")
            title = f"{row_bot} vs {col_bot}: ({cell.row_action}, {cell.col_action})"
            if cell.row_action == "N":
                title += " — proven `none`: the match has no outcome"
            if cell.hypothetical:
                title += " — STIPULATED, not proven"
            cells.append(
                f'<td class="{" ".join(classes)}" title="{html.escape(title)}">'
                f"{cell.row_action}</td>"
            )
        rows.append(
            f'<tr><th class="rowhead">{html.escape(row_bot)}</th>{"".join(cells)}</tr>'
        )
    return (
        f'<table class="matrix"><thead><tr><th></th>{head}</tr></thead>'
        f'<tbody>{"".join(rows)}</tbody></table>'
    )


_CSS = """
:root { color-scheme: light dark; --fg:#1a1a1a; --muted:#666; --bg:#fff;
        --panel:#f7f7f8; --border:#e2e2e5; --c:#0072b2; --d:#d9d9dd; }
@media (prefers-color-scheme: dark) {
  :root { --fg:#e8e8ea; --muted:#a0a0a8; --bg:#16161a; --panel:#1f1f25;
          --border:#33333c; --d:#3a3a44; }
}
* { box-sizing: border-box; }
body { margin:0; padding:2.5rem 1.5rem 4rem; background:var(--bg); color:var(--fg);
       font:15px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,sans-serif; }
main { max-width: 860px; margin: 0 auto; }
h1 { font-size:1.6rem; margin:0 0 .3rem; letter-spacing:-.01em; }
h2 { font-size:1.1rem; margin:2.5rem 0 .4rem; letter-spacing:-.01em; }
.sub { color:var(--muted); margin:0 0 2rem; }
.note { color:var(--muted); font-size:.9rem; margin:.3rem 0 1rem; }
.panel { background:var(--panel); border:1px solid var(--border);
         border-radius:10px; padding:1rem; margin:.6rem 0 0; overflow-x:auto; }
.chart { width:100%; height:auto; display:block; }
.grid { stroke:var(--border); stroke-width:1; }
.line { fill:none; stroke-width:2.2; stroke-linejoin:round; stroke-linecap:round; }
.tick { fill:var(--muted); font-size:11px; }
.legend { fill:var(--fg); font-size:11px; }
.axis { fill:var(--muted); font-size:11px; }
.never { fill:var(--muted); font-size:11px; font-style:italic; }
.end { text-anchor:end; } .mid { text-anchor:middle; }
.cursor-hit { cursor:crosshair; }
.cursor-rule { stroke:var(--muted); stroke-width:1; stroke-dasharray:3 3; }
.cursor-dot { stroke:var(--bg); stroke-width:1.5; }
.cursor-box { fill:var(--bg); stroke:var(--border); stroke-width:1; opacity:.96; }
.cursor-head { fill:var(--fg); font-size:11px; font-weight:600; }
.cursor-row { font-size:11px; }
/* The layer must never eat the pointer events the hit rect is listening for. */
.cursor-layer { pointer-events:none; }
.stats { display:flex; flex-wrap:wrap; gap:.6rem; margin:1.2rem 0 0; padding:0; list-style:none; }
.stats li { background:var(--panel); border:1px solid var(--border); border-radius:8px;
            padding:.6rem .85rem; min-width:130px; }
.stats b { display:block; font-size:1.25rem; letter-spacing:-.02em; }
.stats span { color:var(--muted); font-size:.8rem; }
table.matrix { border-collapse:collapse; font-size:12px; }
table.matrix th, table.matrix td { border:1px solid var(--border); padding:3px 6px;
                                   text-align:center; }
table.matrix .rowhead { text-align:right; font-weight:500; white-space:nowrap; }
table.matrix td.c { background:var(--c); color:#fff; }
table.matrix td.d { background:var(--d); }
/* Proven `= none` — neither C nor D; hatched so it never reads as defection. */
table.matrix td.n { background:repeating-linear-gradient(45deg,
    var(--d), var(--d) 4px, transparent 4px, transparent 8px);
    color:var(--muted); font-style:italic; }
table.matrix td.hyp { outline:2px dashed #d55e00; outline-offset:-2px; }
code { background:var(--panel); padding:.1rem .3rem; border-radius:4px; font-size:.9em; }
.banner { border-radius:8px; padding:.7rem .9rem; margin:1rem 0 0;
          font-size:.88rem; line-height:1.5; border:1px solid; }
.banner.warn { background:rgba(213,94,0,.10); border-color:rgba(213,94,0,.55); }
.banner.ok { background:rgba(0,158,115,.10); border-color:rgba(0,158,115,.5); }
.banner code { background:transparent; padding:0; font-size:.95em; }
.pill { display:inline-block; background:var(--c); color:#fff; font-size:.72rem;
        font-weight:600; padding:.15rem .5rem; border-radius:999px;
        vertical-align:middle; margin-left:.4rem; letter-spacing:0; }
.alpha-control { display:flex; align-items:center; gap:.8rem; flex-wrap:wrap;
                 background:var(--panel); border:1px solid var(--border);
                 border-radius:10px; padding:.7rem 1rem; margin:.6rem 0 0; }
.alpha-control label { color:var(--muted); font-size:.85rem; }
.alpha-control input[type="range"] { flex:1; min-width:180px; accent-color:var(--c); }
.alpha-control input[type="radio"] { accent-color:var(--c); }
.ctl-label { color:var(--muted); font-size:.85rem; }
table.fam { border-collapse:collapse; font-size:.82rem; width:100%; }
table.fam th, table.fam td { border-bottom:1px solid var(--border);
                             padding:6px 10px; text-align:left; vertical-align:top; }
table.fam th { color:var(--muted); font-weight:500; }
"""


def build_report(
    matrix: TauMatrix,
    alphas: tuple[float, ...] = _DEFAULT_ALPHAS,
    families: tuple[str, ...] | None = None,
    zoo: "NamedZoo | None" = None,
) -> str:
    """Render the page. `families` restricts the σ channels (None = all).

    `zoo` is the `NamedZoo` the matrix came from, used only to label the page —
    the numbers all come from `matrix`, so passing it is optional.
    """
    from pd_runner.tau.channels import all_families
    from pd_runner.tau.syntax import syntactic_twins

    fams = all_families(matrix)
    if families is not None:
        unknown = set(families) - set(fams)
        if unknown:
            raise ValueError(f"unknown σ families: {sorted(unknown)}")
        fams = {k: fams[k] for k in families}

    coarse = [round(1.0 - 0.05 * i, 3) for i in range(21)]

    # The pairs each channel can NEVER separate (its transparency ceiling).
    family_twins: dict[str, list[tuple[str, ...]]] = {
        "behavioral": behavioral_twins(matrix),
        "epsilon": [],  # identity-based by construction — no twins possible
        "syntactic": syntactic_twins(matrix),
    }

    # Initial selector positions: the true middle of the requested alphas
    # snapped to the slider grid (lower-middle for an even-length tuple — the
    # upper-middle once silently rendered a different α than a reader scanning
    # the list expected), and the behavioral channel when present.
    mid_alpha = sorted(alphas)[(len(alphas) - 1) // 2]
    initial_alpha = min(_SLIDER_ALPHAS, key=lambda a: (abs(a - mid_alpha), a))
    initial_index = _SLIDER_ALPHAS.index(initial_alpha)
    initial_family = "behavioral" if "behavioral" in fams else next(iter(fams))
    # The t cursor opens at the MIDDLE of the dial rather than at full
    # transparency: at t = 1 the anchor theorem makes every deviation zero, so
    # the deviation views would open completely blank and read as broken.
    initial_transparency = _SLIDER_TRANSPARENCIES[len(_SLIDER_TRANSPARENCIES) // 2]
    initial_t_index = _SLIDER_TRANSPARENCIES.index(initial_transparency)

    # ---- pre-rendered swap views (the page is static; ~20 lines of inline JS
    # toggle `hidden` by the two sliders and the family radio) ---------------
    def swap_view(content: str, *, alpha: float | None = None,
                  family: str | None = None,
                  transparency: float | None = None) -> str:
        attrs, hidden = "", False
        if alpha is not None:
            attrs += f' data-alpha="{alpha:g}"'
            hidden = hidden or alpha != initial_alpha
        if family is not None:
            attrs += f' data-family="{family}"'
            hidden = hidden or family != initial_family
        if transparency is not None:
            attrs += f' data-transparency="{transparency:g}"'
            hidden = hidden or transparency != initial_transparency
        return (
            f'<div class="panel swap-view"{attrs}{" hidden" if hidden else ""}>'
            f"{content}</div>"
        )

    # 1 · per family: one line per α over the fine grid.
    line_views = "".join(
        swap_view(
            _line_chart(
                [
                    (
                        f"α = {alpha:g}",
                        [(p.target_transparency, p.mutual_coop_rate)
                         for p in sweep_by_transparency(matrix, alpha, family=fam)],
                        _SERIES_COLORS[i % len(_SERIES_COLORS)],
                    )
                    for i, alpha in enumerate(alphas)
                ],
                y_label="mutual cooperation rate",
            ),
            family=key,
        )
        for key, fam in fams.items()
    )

    # 2 · per α: one line per family — the matched-MI channel comparison.
    comparison_views = "".join(
        swap_view(
            _line_chart(
                [
                    (
                        fam.label,
                        [(p.target_transparency, p.mutual_coop_rate)
                         for p in sweep_by_transparency(matrix, a, coarse, family=fam)],
                        _FAMILY_COLORS.get(key, "#009e73"),
                    )
                    for key, fam in fams.items()
                ],
                y_label="mutual cooperation rate",
            ),
            alpha=a,
        )
        for a in _SLIDER_ALPHAS
    )

    # 3 / 4 · per (family, α).
    comp_views = "".join(
        swap_view(_composition_chart(matrix, a, coarse, family=fam),
                  alpha=a, family=key)
        for key, fam in fams.items()
        for a in _SLIDER_ALPHAS
    )

    # 3b · per (family, α, t): each bot's own row split into the four pairs.
    # This one needs BOTH cursors — the composition of a bot's row is a point
    # in the (t, α) plane, not a curve — hence the transparency slider.
    per_bot_views = "".join(
        swap_view(
            _per_bot_composition_chart(
                per_bot_composition(matrix, a, t, family=fam)
            ),
            alpha=a, family=key, transparency=t,
        )
        for key, fam in fams.items()
        for a in _SLIDER_ALPHAS
        for t in _SLIDER_TRANSPARENCIES
    )

    threshold_views = "".join(
        swap_view(
            _threshold_chart(
                robustness_thresholds(matrix, a, coarse, family=fam),
                row_deviation(matrix, a, coarse, family=fam),
            ),
            alpha=a, family=key,
        )
        for key, fam in fams.items()
        for a in _SLIDER_ALPHAS
    )

    # 4b · the α-axis transpose of chart 4: t is the cursor, α is the axis.
    alpha_dev_views = "".join(
        swap_view(
            _alpha_deviation_chart(
                alpha_deviation(matrix, t, _SLIDER_ALPHAS, family=fam)
            ),
            family=key, transparency=t,
        )
        for key, fam in fams.items()
        for t in _SLIDER_TRANSPARENCIES
    )

    # 5 · per family.
    phase_views = "".join(
        swap_view(_phase_diagram(matrix, list(alphas), coarse, family=fam),
                  family=key)
        for key, fam in fams.items()
    )

    family_rows = "".join(
        f"<tr><td><b>{html.escape(fam.label)}</b></td>"
        f"<td>{fam.ceiling():.1%}</td>"
        f"<td>{html.escape(', '.join('/'.join(g) for g in family_twins.get(key, [])) or '—')}</td>"
        f"<td>{html.escape(fam.description)}</td></tr>"
        for key, fam in fams.items()
    )
    family_radios = "".join(
        f'<label><input type="radio" name="family" value="{key}"'
        f'{" checked" if key == initial_family else ""}> {html.escape(fam.label)}</label>'
        for key, fam in fams.items()
    )
    initial_family_label = fams[initial_family].label

    def alpha_slider(caption: str) -> str:
        """One α control. Every copy is kept in sync by `control_script`.

        Charts 2–4 each get their own below the plot so α can be adjusted
        where it is being read, without scrolling back to the top control.
        """
        return (
            f'<div class="alpha-control">'
            f'<label>{caption}</label>'
            f'<input type="range" class="alpha-slider" min="0" '
            f'max="{len(_SLIDER_ALPHAS) - 1}" step="1" value="{initial_index}">'
            f'<span class="pill alpha-readout">α = {initial_alpha:g}</span>'
            f"</div>"
        )

    def transparency_slider(caption: str) -> str:
        """The t cursor, for the views that are a POINT in the (t, α) plane.

        Runs high-index = opaque so dragging right degrades the signal, matching
        every x-axis on the page (full transparency on the left).
        """
        return (
            f'<div class="alpha-control">'
            f"<label>{caption}</label>"
            f'<input type="range" class="t-slider" min="0" '
            f'max="{len(_SLIDER_TRANSPARENCIES) - 1}" step="1" '
            f'value="{initial_t_index}">'
            f'<span class="pill t-readout">t = {initial_transparency:.0%}</span>'
            f"</div>"
        )

    alphas_js = "[" + ",".join(f'"{a:g}"' for a in _SLIDER_ALPHAS) + "]"
    ts_js = "[" + ",".join(f'"{t:g}"' for t in _SLIDER_TRANSPARENCIES) + "]"
    labels_js = "{" + ",".join(f'"{k}":"{fam.label}"' for k, fam in fams.items()) + "}"
    # Plain string (not an f-string): JS braces stay literal; values are
    # interpolated into the surrounding template instead.
    control_script = (
        "<script>(function () {\n"
        f"  var alphas = {alphas_js};\n"
        f"  var ts = {ts_js};\n"
        f"  var labels = {labels_js};\n"
        '  var sliders = document.querySelectorAll(".alpha-slider");\n'
        '  var tSliders = document.querySelectorAll(".t-slider");\n'
        "  var value = sliders.length ? +sliders[0].value : 0;\n"
        "  var tValue = tSliders.length ? +tSliders[0].value : 0;\n"
        "  function show() {\n"
        "    var a = alphas[value];\n"
        "    var t = ts[tValue];\n"
        "    var f = document.querySelector('input[name=\"family\"]:checked').value;\n"
        '    document.querySelectorAll(".swap-view").forEach(function (el) {\n'
        "      var byAlpha = el.dataset.alpha !== undefined && el.dataset.alpha !== a;\n"
        "      var byFamily = el.dataset.family !== undefined && el.dataset.family !== f;\n"
        "      var byT = el.dataset.transparency !== undefined"
        " && el.dataset.transparency !== t;\n"
        "      el.hidden = byAlpha || byFamily || byT;\n"
        "    });\n"
        # Every duplicated slider tracks the shared value, so moving any one of
        # them leaves the others (and their readouts) consistent.
        "    sliders.forEach(function (s) { if (+s.value !== value) s.value = value; });\n"
        "    tSliders.forEach(function (s) { if (+s.value !== tValue) s.value = tValue; });\n"
        '    document.querySelectorAll(".alpha-readout").forEach(function (el) {\n'
        '      el.textContent = "α = " + a;\n'
        "    });\n"
        '    document.querySelectorAll(".t-readout").forEach(function (el) {\n'
        '      el.textContent = "t = " + Math.round(+t * 100) + "%";\n'
        "    });\n"
        '    document.querySelectorAll(".family-readout").forEach(function (el) {\n'
        "      el.textContent = labels[f];\n"
        "    });\n"
        "  }\n"
        "  sliders.forEach(function (s) {\n"
        '    s.addEventListener("input", function () { value = +s.value; show(); });\n'
        "  });\n"
        "  tSliders.forEach(function (s) {\n"
        '    s.addEventListener("input", function () { tValue = +s.value; show(); });\n'
        "  });\n"
        "  document.querySelectorAll('input[name=\"family\"]').forEach(function (r) {\n"
        '    r.addEventListener("change", show);\n'
        "  });\n"
        "  show();\n"
        "})();</script>"
    )

    twins = family_twins["behavioral"]
    stipulated = len({tuple(sorted(p)) for p in matrix.hypothetical_cells})

    # A page that leaves the author's hands must carry its own caveat: the
    # one-line provenance note is too easy to skim past when a reader arrives
    # at a shared link with no briefing.
    if matrix.is_fully_proven:
        provenance_banner = (
            '<p class="banner ok">Every cell in this matrix is a theorem '
            "machine-checked by the Lean kernel.</p>"
        )
    else:
        pairs = ", ".join(
            f"{a} vs {b}"
            for a, b in sorted({tuple(sorted(p)) for p in matrix.hypothetical_cells})
        )
        provenance_banner = (
            f'<p class="banner warn"><b>Results below are CONDITIONAL.</b> '
            f"{stipulated} of this zoo's outcome pairs are <i>stipulated</i> — "
            f"assumed, not proven — because their Lean proofs do not exist yet: "
            f"<code>{html.escape(pairs)}</code>. Everything else is "
            f"machine-checked. Any claim taken from this page should be "
            f"reported as resting on those assumptions.</p>"
        )

    # A proven `= none` cell (MirrorBot self-play) is a fifth state, neither
    # cooperation nor defection; call it out so "N" in the matrix is not read
    # as a rendering glitch.
    none_pairs = sorted(
        {
            tuple(sorted((r, c)))
            for r in matrix.bots
            for c in matrix.bots
            if matrix.cell(r, c).row_action == "N"
        }
    )
    none_note = (
        f'<p class="note">No-outcome cells (proven <code>= none</code>, shown as '
        f'<code>N</code>): {html.escape(", ".join(" vs ".join(p) for p in none_pairs))}. '
        f"These matches have no fixpoint at all; the tau layer reads them "
        f"pessimistically (an <code>N</code> hypothesis contributes no "
        f"cooperation mass).</p>"
        if none_pairs
        else ""
    )

    zoo_line = (
        f'<p class="note">Sub-zoo: <b>{html.escape(zoo.label)}</b> — '
        f"{html.escape(zoo.description)}</p>"
        if zoo is not None
        else ""
    )

    return f"""<title>TauBots — graded transparency{
        f" ({html.escape(zoo.label)})" if zoo is not None else ""}</title>
<style>{_CSS}</style>
<main>
<h1>TauBots — graded transparency over the zoo</h1>
<p class="sub">Def 3 tau lift over the Lean-verified outcome matrix ·
{len(matrix)} bots · {len(matrix) ** 2} ordered cells</p>
{zoo_line}
<p class="note">Zoo: <code>{html.escape(", ".join(matrix.bots))}</code></p>
{none_note}

<ul class="stats">
  <li><b>{len(matrix)}</b><span>bots in the zoo</span></li>
  <li><b>{len(fams)}</b><span>σ channel families</span></li>
  <li><b>{len(twins)}</b><span>behavioral twin groups</span></li>
  <li><b>{stipulated}</b><span>stipulated pairs</span></li>
</ul>
{provenance_banner}

<h2>σ channel families</h2>
<p class="note">A σ family is (what leaks) × (how it blurs). Every family is
calibrated onto the SAME transparency dial t ∈ [0, 1] (normalized mutual
information), so at equal t the information rate is identical and only the
confusion structure — WHICH bots get mistaken for which — differs. A ceiling
below 100% means that family has twins it can never separate.</p>
<div class="panel"><table class="fam">
<thead><tr><th>family</th><th>ceiling</th><th>unseparable twins</th><th>what leaks</th></tr></thead>
<tbody>{family_rows}</tbody></table></div>

<div class="alpha-control">
  <span class="ctl-label">σ family</span> {family_radios}
</div>
{alpha_slider("caution threshold α — drives charts 2, 3 and 4")}

<h2>1 · Cooperation vs transparency <span class="pill family-readout">{html.escape(initial_family_label)}</span></h2>
<p class="note">Mutual-cooperation rate as the signal degrades, one line per
caution threshold α, under the selected σ family. The x-axis is normalized
mutual information, not a raw knob — knobs are unitless and family-specific.</p>
{line_views}

<h2>2 · Channel comparison at matched transparency <span class="pill alpha-readout">α = {initial_alpha:g}</span></h2>
<p class="note">One line per σ family at the selected α. Because every family
is calibrated to the same MI dial, the gap between curves at equal x is purely
the effect of confusion STRUCTURE — e.g. the value of reading source over
watching play. The ε-uniform control has no structure at all: divergence from
it is what "similarity matters" looks like.</p>
{comparison_views}
{alpha_slider("α for this chart — synced with every other α control")}

<h2>3 · What cooperation displaces <span class="pill family-readout">{html.escape(initial_family_label)}</span> <span class="pill alpha-readout">α = {initial_alpha:g}</span></h2>
<p class="note">The same tournaments, split into all three game outcomes.
Chart 1 counts only (C,C), which hides <em>which</em> outcome it is displacing.
Watch the orange band: as the signal degrades, exploitation converts into
cooperation — bots fooled into cooperating with defectors — so a rising blue
band at low transparency is not cooperation improving. Inside the dashed region
every bot plays unconditionally (the classical-PD limit).</p>
{comp_views}
{alpha_slider("α for this chart — synced with every other α control")}

<h2>3b · Outcome mix per bot <span class="pill family-readout">{html.escape(initial_family_label)}</span> <span class="pill alpha-readout">α = {initial_alpha:g}</span> <span class="pill t-readout">t = {initial_transparency:.0%}</span></h2>
<p class="note">The same tournament as chart 3, but broken out by bot instead
of aggregated: each bar is one bot's own row, counting how many of its
{len(matrix)} opponents it ends up in each outcome pair with. The first letter
is always <em>this bot's</em> action, so <code>(D,C)</code> (it exploited
someone) and <code>(C,D)</code> (it got exploited) stay separate — chart 3
pools them, which is right for a tournament total and wrong per bot. Both
cursors matter here: a bot's mix is a point in the (t, α) plane, not a curve
over one dial.</p>
{per_bot_views}
{alpha_slider("α for this chart — synced with every other α control")}
{transparency_slider("transparency t for this chart — synced with chart 4b")}

<h2>4 · How much transparency each bot needs <span class="pill family-readout">{html.escape(initial_family_label)}</span> <span class="pill alpha-readout">α = {initial_alpha:g}</span></h2>
<p class="note">Each row is one bot across the whole transparency axis, shaded
by how much of its row differs from the base matrix there (normalized Hamming
distance). The <strong>tick</strong> marks the <em>first</em> departure from
its base-matrix row; a tick further right means it holds its behavior further
into the blur. Colour is the drift's size: a one-cell flip and a row inversion
cross at the same tick but end up very differently. Constant bots never deviate
— they have no conditionality to lose — and stay grey the whole way.</p>
<p class="note"><strong>Read the strip, not just the tick.</strong> Deviation is
<em>not</em> monotone in transparency, so a departure need not be permanent: a
row marked <code>°</code> returns to its base behavior at some lower
transparency. That is not noise. As transparency → 0 every signal converges to
the same uniform mixture, so every opponent's cooperation mass converges to one
shared limit — the bot's own base cooperation fraction — and masses reaching it
from opposite sides can flip two cells in opposite directions at nearby
budgets, dipping the deviation count. <strong>These thresholds are α- and
channel-sensitive</strong> — the ranking changes with the caution threshold and
with what leaks, so this chart is one slice of chart 5, not a property of the
bots alone.</p>
{threshold_views}
{alpha_slider("α for this chart — synced with every other α control")}

<h2>4b · How much caution each bot can afford <span class="pill family-readout">{html.escape(initial_family_label)}</span> <span class="pill t-readout">t = {initial_transparency:.0%}</span></h2>
<p class="note">Chart 4 transposed: transparency is now the cursor and α is the
axis, so this reads off <em>for which caution thresholds</em> each bot stops
behaving like its base bot at the transparency you have fixed. Same colour
scale as chart 4 — grey means the tau bot's row is identical to the base bot's,
warmth is the fraction of the row that differs. Together the two charts cover
the (t, α) plane one bot at a time, which chart 5's aggregate necessarily
averages away.</p>
{alpha_dev_views}
{transparency_slider("transparency t for this chart — synced with chart 3b")}

<h2>5 · (transparency, α) phase diagram <span class="pill family-readout">{html.escape(initial_family_label)}</span></h2>
<p class="note">The two dials crossed, under the selected σ family.
Transparency is a property of the environment; α is the agent's own caution.
Hover a cell for its value.</p>
{phase_views}

<h2>6 · The underlying outcome matrix</h2>
<p class="note">Each cell shows what the ROW bot plays against the column bot.
Blue = cooperate. Hatched <code>N</code> = proven <code>none</code>, a match with
no outcome. Dashed outline = stipulated, not proven.</p>
<div class="panel">{_matrix_table(matrix)}</div>

<h2>Notes</h2>
<p class="note">
Behavioral twin groups: {html.escape(str([list(g) for g in twins]) if twins else "none — behavior identifies every bot")}.
Each channel family has its own unseparable twins (see the family table): the
behavioral channel cannot split bots with identical action rows, the syntactic
channel cannot split bots with identical ASTs (budget arguments are erased, so
two bots differing only in their search budget are one program to it), and the
ε-uniform control separates everything, having no structure to be blind
through.<br><br>
α sweeps should step <em>between</em> breakpoints, never on them: when α sits
exactly on an agent's achievable cooperation mass, float residue decides the
play and the agent looks conditional when it is not.
</p>
</main>
{control_script}
{_CURSOR_SCRIPT}"""


def main() -> None:
    import argparse
    import subprocess

    parser = argparse.ArgumentParser(description="Build the tau HTML report.")
    parser.add_argument("--output", type=Path, default=Path("generated/tau_report.html"))
    parser.add_argument("--alphas", type=str, default="0.3,0.45,0.62,0.8")
    parser.add_argument(
        "--zoo",
        type=str,
        default=DEFAULT_ZOO,
        choices=sorted(ZOOS),
        help="which sub-zoo to analyse (see pd_runner.tau.matrix.ZOOS)",
    )
    parser.add_argument("--open", action="store_true", help="open in the browser")
    args = parser.parse_args()

    zoo = get_zoo(args.zoo)
    alphas = tuple(float(a) for a in args.alphas.split(","))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        build_report(zoo.load(), alphas, zoo=zoo), encoding="utf-8"
    )
    print(f"wrote {args.output}  (zoo: {zoo.label})")
    if args.open:
        subprocess.run(["open", str(args.output)], check=False)


if __name__ == "__main__":
    main()

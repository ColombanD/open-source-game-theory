"""Visual report for the tau layer — a self-contained HTML page.

Deliberately dependency-free: the charts are hand-rolled inline SVG, so the
report runs with no matplotlib/plotly in the environment and the output is a
single file that opens anywhere.

    uv run python -m pd_runner.tau.report
    uv run python -m pd_runner.tau.report --output ~/tau.html --open

Four views, in the order the argument runs:

1. **Cooperation vs transparency** — the headline. Mutual-cooperation rate as
   the signal degrades, one line per α. Plotted on the TRANSPARENCY axis
   (normalized MI), not raw temperature, because t is unitless and its scale
   depends on the zoo.
2. **Robustness thresholds** — the transparency at which each bot first departs
   from its base-matrix row. This is where "how much transparency does Löbian
   cooperation need?" gets answered per agent.
3. **(t, α) phase diagram** — the two dials crossed, coloured by mutual
   cooperation rate.
4. **The outcome matrix itself** — what everything above is computed from,
   with stipulated cells marked.
"""

from __future__ import annotations

import html
from dataclasses import dataclass
from pathlib import Path

from pd_runner.tau.matrix import TauMatrix, load_tau_matrix
from pd_runner.tau.signal import (
    behavioral_distance_matrix,
    behavioral_twins,
    transparency,
)
from pd_runner.tau.sweep import run_tournament

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

# Colour-blind-safe qualitative colours (Okabe–Ito).
_SERIES_COLORS = ("#0072b2", "#d55e00", "#009e73", "#cc79a7", "#e69f00")


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
) -> list[SweepPoint]:
    """One tournament per dial value; the dial IS the transparency target."""
    distances = behavioral_distance_matrix(matrix)
    points = []
    for target in targets if targets is not None else _TRANSPARENCY_GRID:
        result = run_tournament(matrix, target, alpha, distances)
        points.append(SweepPoint(
            target_transparency=target,
            temperature=result.temperature,
            actual_transparency=result.transparency,
            mutual_coop_rate=result.mutual_coop_rate,
            coop_rate=result.coop_rate,
            degenerate=result.is_degenerate,
        ))
    return points


def robustness_thresholds(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float] | None = None,
) -> dict[str, float | None]:
    """Transparency at which each bot first departs from its base-matrix row.

    `None` means the bot never deviates — its behavior is blur-proof at this α
    (true of the constant bots, which have no conditionality to lose).
    """
    distances = behavioral_distance_matrix(matrix)
    base = {b: tuple(matrix.action(b, o) for o in matrix.bots) for b in matrix.bots}
    thresholds: dict[str, float | None] = dict.fromkeys(matrix.bots)
    for target in targets if targets is not None else _TRANSPARENCY_GRID:
        result = run_tournament(matrix, target, alpha, distances)
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
) -> str:
    """Inline SVG line chart. `series` = [(label, [(x, y)…], colour)]."""
    pad_l, pad_r, pad_t, pad_b = 56, 130, 16, 44
    plot_w, plot_h = width - pad_l - pad_r, height - pad_t - pad_b

    # x runs 1.0 (full transparency) on the LEFT down to 0.0 on the right, so
    # the reader moves left-to-right in the direction of degrading signal.
    def sx(x: float) -> float:
        return pad_l + (1.0 - x) * plot_w

    def sy(y: float) -> float:
        return pad_t + (1.0 - y) * plot_h

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']

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
    parts.append("</svg>")
    return "".join(parts)


def _threshold_chart(thresholds: dict[str, float | None], width: int = 720) -> str:
    """Horizontal bars: how much transparency each bot needs to behave as itself."""
    ordered = sorted(
        thresholds.items(),
        key=lambda kv: (kv[1] is None, -(kv[1] or 0.0)),
    )
    row_h, pad_l, pad_r, pad_t = 26, 130, 60, 12
    height = pad_t + row_h * len(ordered) + 28
    plot_w = width - pad_l - pad_r

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    for frac in (0.0, 0.25, 0.5, 0.75, 1.0):
        x = pad_l + frac * plot_w
        parts.append(
            f'<line x1="{x:.1f}" y1="{pad_t}" x2="{x:.1f}" '
            f'y2="{pad_t + row_h * len(ordered)}" class="grid"/>'
            f'<text x="{x:.1f}" y="{height - 8}" class="tick mid">{frac:.0%}</text>'
        )

    for i, (bot, value) in enumerate(ordered):
        y = pad_t + i * row_h
        parts.append(
            f'<text x="{pad_l - 10}" y="{y + 17}" class="tick end">{html.escape(bot)}</text>'
        )
        if value is None:
            parts.append(
                f'<text x="{pad_l + 6}" y="{y + 17}" class="never">'
                f'never deviates (unconditional)</text>'
            )
        else:
            parts.append(
                f'<rect x="{pad_l}" y="{y + 5}" width="{value * plot_w:.1f}" '
                f'height="{row_h - 12}" rx="3" fill="#0072b2" opacity="0.75"/>'
                f'<text x="{pad_l + value * plot_w + 8:.1f}" y="{y + 17}" '
                f'class="tick">{value:.0%}</text>'
            )
    parts.append("</svg>")
    return "".join(parts)


_COMPOSITION_BANDS = (
    ("CC", "#0072b2", "mutual cooperation (C,C)"),
    ("exploit", "#e69f00", "exploitation (C,D) + (D,C)"),
    ("DD", "#8c8c96", "mutual defection (D,D)"),
)


def _composition_chart(
    matrix: TauMatrix,
    alpha: float,
    targets: list[float],
    width: int = 720,
    height: int = 300,
) -> str:
    """Stacked bands showing what the non-cooperative cells actually are.

    The headline rate only counts (C,C). Splitting out exploitation and mutual
    defection reveals WHICH outcome cooperation is displacing as blur rises —
    the difference between real cooperation and bots being fooled.
    """
    distances = behavioral_distance_matrix(matrix)
    pad_l, pad_r, pad_t, pad_b = 56, 200, 16, 44
    plot_w, plot_h = width - pad_l - pad_r, height - pad_t - pad_b

    def sx(x: float) -> float:
        return pad_l + (1.0 - x) * plot_w

    def sy(y: float) -> float:
        return pad_t + (1.0 - y) * plot_h

    samples = []
    for target in targets:
        result = run_tournament(matrix, target, alpha, distances)
        samples.append((target, result.composition, result.is_degenerate))

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']

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
        parts.append(
            f'<rect x="{sx(max(degenerate)):.1f}" y="{pad_t}" '
            f'width="{pad_l + plot_w - sx(max(degenerate)):.1f}" height="{plot_h}" '
            f'fill="none" stroke="#d55e00" stroke-width="1.5" '
            f'stroke-dasharray="4 3"/>'
            f'<text x="{sx(max(degenerate)) + 6:.1f}" y="{pad_t + 14}" '
            f'class="tick" fill="#d55e00">degenerate</text>'
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
    parts.append("</svg>")
    return "".join(parts)


def _phase_diagram(
    matrix: TauMatrix,
    alphas: list[float],
    targets: list[float],
    width: int = 720,
) -> str:
    """Heatmap of mutual cooperation over the (transparency, α) grid."""
    distances = behavioral_distance_matrix(matrix)
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
            rate = run_tournament(matrix, target, alpha, distances).mutual_coop_rate
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
            classes = ["c" if cell.row_action == "C" else "d"]
            if cell.hypothetical:
                classes.append("hyp")
            title = f"{row_bot} vs {col_bot}: ({cell.row_action}, {cell.col_action})"
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
table.matrix td.hyp { outline:2px dashed #d55e00; outline-offset:-2px; }
code { background:var(--panel); padding:.1rem .3rem; border-radius:4px; font-size:.9em; }
.pill { display:inline-block; background:var(--c); color:#fff; font-size:.72rem;
        font-weight:600; padding:.15rem .5rem; border-radius:999px;
        vertical-align:middle; margin-left:.4rem; letter-spacing:0; }
.alpha-control { display:flex; align-items:center; gap:.8rem; flex-wrap:wrap;
                 background:var(--panel); border:1px solid var(--border);
                 border-radius:10px; padding:.7rem 1rem; margin:2.2rem 0 0; }
.alpha-control label { color:var(--muted); font-size:.85rem; }
.alpha-control input[type="range"] { flex:1; min-width:180px; accent-color:var(--c); }
"""


def build_report(matrix: TauMatrix, alphas: tuple[float, ...] = _DEFAULT_ALPHAS) -> str:
    twins = behavioral_twins(matrix)
    ceiling = transparency(matrix, 0.0)
    coarse = [round(1.0 - 0.05 * i, 3) for i in range(21)]

    series = [
        (
            f"α = {alpha:g}",
            [(p.target_transparency, p.mutual_coop_rate)
             for p in sweep_by_transparency(matrix, alpha)],
            _SERIES_COLORS[i % len(_SERIES_COLORS)],
        )
        for i, alpha in enumerate(alphas)
    ]
    # The slider's starting position: the true middle of the requested alphas
    # (lower-middle for an even-length tuple — the upper-middle silently showed
    # a different α than a reader scanning the list expected), snapped to the
    # slider grid. Thresholds are α-sensitive, so the initial value is stated
    # on the charts and every grid value is one drag away.
    mid_alpha = sorted(alphas)[(len(alphas) - 1) // 2]
    initial_alpha = min(_SLIDER_ALPHAS, key=lambda a: (abs(a - mid_alpha), a))

    # Pre-render the two single-α panels at every slider value; the slider
    # swaps them client-side (`hidden` attribute), so the page needs no server.
    def alpha_views(render) -> str:
        return "".join(
            f'<div class="panel alpha-view" data-alpha="{a:g}"'
            f'{"" if a == initial_alpha else " hidden"}>{render(a)}</div>'
            for a in _SLIDER_ALPHAS
        )

    comp_views = alpha_views(lambda a: _composition_chart(matrix, a, coarse))
    threshold_views = alpha_views(
        lambda a: _threshold_chart(robustness_thresholds(matrix, a, coarse))
    )

    initial_index = _SLIDER_ALPHAS.index(initial_alpha)
    alphas_js = "[" + ",".join(f'"{a:g}"' for a in _SLIDER_ALPHAS) + "]"
    # Plain string (not an f-string): JS braces stay literal; values are
    # interpolated into the surrounding template instead.
    slider_script = (
        "<script>(function () {\n"
        f"  var alphas = {alphas_js};\n"
        '  var slider = document.getElementById("alpha-slider");\n'
        "  function show() {\n"
        "    var a = alphas[+slider.value];\n"
        '    document.querySelectorAll(".alpha-view").forEach(function (el) {\n'
        "      el.hidden = el.dataset.alpha !== a;\n"
        "    });\n"
        '    document.querySelectorAll(".alpha-readout").forEach(function (el) {\n'
        '      el.textContent = "α = " + a;\n'
        "    });\n"
        "  }\n"
        '  slider.addEventListener("input", show);\n'
        "  show();\n"
        "})();</script>"
    )

    stipulated = len({tuple(sorted(p)) for p in matrix.hypothetical_cells})
    provenance = (
        "every cell machine-checked by Lean"
        if matrix.is_fully_proven
        else f"{stipulated} stipulated pair(s) — results are CONDITIONAL"
    )

    return f"""<title>TauBots — graded transparency</title>
<style>{_CSS}</style>
<main>
<h1>TauBots — graded transparency over the zoo</h1>
<p class="sub">Def 3 tau lift over the Lean-verified outcome matrix ·
{len(matrix)} bots · {len(matrix) ** 2} ordered cells</p>
<p class="note">Zoo: <code>{html.escape(", ".join(matrix.bots))}</code></p>

<ul class="stats">
  <li><b>{len(matrix)}</b><span>bots in the zoo</span></li>
  <li><b>{ceiling:.0%}</b><span>transparency ceiling</span></li>
  <li><b>{len(twins)}</b><span>behavioral twin groups</span></li>
  <li><b>{stipulated}</b><span>stipulated pairs</span></li>
</ul>
<p class="note">Provenance: {provenance}.</p>

<h2>1 · Cooperation vs transparency</h2>
<p class="note">Mutual-cooperation rate as the signal degrades, one line per
caution threshold α. The x-axis is normalized mutual information, not raw
temperature — t is unitless and its scale depends on the zoo.</p>
<div class="panel">{_line_chart(series, y_label="mutual cooperation rate")}</div>

<div class="alpha-control">
  <label for="alpha-slider">caution threshold α — drives charts 2 and 3</label>
  <input type="range" id="alpha-slider" min="0" max="{len(_SLIDER_ALPHAS) - 1}"
         step="1" value="{initial_index}">
  <span class="pill alpha-readout">α = {initial_alpha:g}</span>
</div>

<h2>2 · What cooperation displaces <span class="pill alpha-readout">α = {initial_alpha:g}</span></h2>
<p class="note">The same tournaments, split into all three game outcomes.
Chart 1 counts only (C,C), which hides <em>which</em> outcome it is displacing.
Watch the orange band: as the signal degrades, exploitation converts into
cooperation — bots fooled into cooperating with defectors — so a rising blue
band at low transparency is not cooperation improving. Inside the dashed region
every bot plays unconditionally (the classical-PD limit), where these numbers
reflect the loss of conditioning rather than a transparency effect.</p>
{comp_views}

<h2>3 · How much transparency each bot needs <span class="pill alpha-readout">α = {initial_alpha:g}</span></h2>
<p class="note">Transparency at which each bot first departs from its
base-matrix row. Longer bar = needs a clearer signal to behave as itself.
Constant bots never deviate: they have no conditionality to lose.
<strong>These thresholds are α-sensitive</strong> — the ranking changes with the
caution threshold (drag the slider above to see it), so this chart is one slice
of chart 4, not a property of the bots alone.</p>
{threshold_views}

<h2>4 · (transparency, α) phase diagram</h2>
<p class="note">The two dials crossed. Transparency is a property of the
environment; α is the agent's own caution. Hover a cell for its value.</p>
<div class="panel">{_phase_diagram(matrix, list(alphas), coarse)}</div>

<h2>5 · The underlying outcome matrix</h2>
<p class="note">Each cell shows what the ROW bot plays against the column bot.
Blue = cooperate. Dashed outline = stipulated, not proven.</p>
<div class="panel">{_matrix_table(matrix)}</div>

<h2>Notes</h2>
<p class="note">
Twin groups: {html.escape(str([list(g) for g in twins]) if twins else "none — behavior identifies every bot")}.
Behaviorally identical bots cannot be separated by any signal at any
temperature, so they cap the transparency scale below 100%.<br><br>
α sweeps should step <em>between</em> breakpoints, never on them: when α sits
exactly on an agent's achievable cooperation mass, float residue decides the
play and the agent looks conditional when it is not.
</p>
</main>
{slider_script}"""


def main() -> None:
    import argparse
    import subprocess

    parser = argparse.ArgumentParser(description="Build the tau HTML report.")
    parser.add_argument("--output", type=Path, default=Path("generated/tau_report.html"))
    parser.add_argument("--alphas", type=str, default="0.3,0.45,0.62,0.8")
    parser.add_argument("--open", action="store_true", help="open in the browser")
    args = parser.parse_args()

    matrix = load_tau_matrix()
    alphas = tuple(float(a) for a in args.alphas.split(","))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(build_report(matrix, alphas), encoding="utf-8")
    print(f"wrote {args.output}")
    if args.open:
        subprocess.run(["open", str(args.output)], check=False)


if __name__ == "__main__":
    main()

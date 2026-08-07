"""HTML report over a finished EGT sweep.

The counterpart to `tau/report.py`, and deliberately built the same way: one
self-contained page, inline SVG, no external assets, light/dark from the same
CSS-variable palette. What differs is the input — the tau report computes its
own tournaments, whereas this one READS a sweep that already ran, because the
four analysis stages cost minutes and their artefacts are the record.

The page is organized around a **(t, α) picker**. Every analysed matrix is
pre-rendered into a hidden panel tagged with `data-cell`; moving either slider
just toggles which panel is visible. No server round-trip, no recomputation —
the same trick `tau/report.py` uses for its α slider, and the reason the page
works from `file://`.

Grid points that shared a matrix (dedup) resolve to the same panel, so the
picker never lands on a hole: `_cell_index` maps every requested `(t, α)` to
the run that actually covers it.

Colour obligations (validated with the dataviz palette checker on the Okabe-Ito
set this repo already uses): the worst adjacent CVD pair sits in the 6-8 band
and two hues fall under 3:1 against the surface, so every chart here ships
direct labels AND a table view. That is a requirement, not a preference.
"""

from __future__ import annotations

import html
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence

# Okabe-Ito, the same order `tau/report.py` uses so a bot keeps its colour
# across the two reports. Assigned in fixed order, never cycled.
_SERIES_COLORS = ("#0072b2", "#d55e00", "#009e73", "#cc79a7", "#e69f00")

# Outcome-class colours. Cooperation is the one hue that carries meaning
# across the whole project (it matches the tau report's `--c`).
_C_BLUE = "#0072b2"
_EXPLOIT = "#e69f00"
_D_GREY = "#8c8c96"


# --------------------------------------------------------------------------
# Loading a sweep from disk
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Cell:
    """One analysed matrix, as recorded in its `summary.json`."""

    run: str
    zoo: str
    t: float
    alpha: float
    fingerprint: str
    n_types: int
    bots: tuple[str, ...]
    excluded_bots: tuple[str, ...]
    is_fully_proven: bool
    grid_points: tuple[tuple[float, float], ...]
    ok: bool
    stages: dict
    run_dir: Path

    @property
    def n_pure_ess(self) -> int | None:
        return self._stage_value("ess", "n_pure_ess")

    @property
    def edges_strict(self) -> int | None:
        return self._stage_value("invasion", "edges_strict")

    @property
    def n_sccs(self) -> int | None:
        return self._stage_value("invasion", "n_sccs")

    @property
    def n_cycles(self) -> int | None:
        return self._stage_value("invasion", "n_cycles")

    @property
    def n_supports(self) -> int | None:
        return self._stage_value("faces", "n_supports")

    @property
    def n_extreme_ne(self) -> int | None:
        return self._stage_value("nash", "n_extreme_NE")

    @property
    def n_components(self) -> int | None:
        return self._stage_value("nash", "n_components")

    @property
    def stable_faces(self) -> int | None:
        by_class = self._stage_value("faces", "by_class")
        if by_class is None:
            return None
        return sum(v for k, v in by_class.items() if k.startswith("asymp_stable"))

    @property
    def faces_by_class(self) -> dict:
        return self._stage_value("faces", "by_class") or {}

    @property
    def enumeration_complete(self) -> bool:
        value = self._stage_value("faces", "enumeration_complete")
        return True if value is None else bool(value)

    @property
    def cross_check_performed(self) -> bool | None:
        return self._stage_value("nash", "cross_check_performed")

    def _stage_value(self, stage: str, key: str):
        entry = self.stages.get(stage)
        if not entry or not entry.get("ok"):
            return None
        return entry.get(key)

    def failed_stages(self) -> list[str]:
        return [k for k, v in self.stages.items() if not v.get("ok")]

    def ran_stages(self) -> list[str]:
        return list(self.stages)


def load_sweep(out_root: Path) -> tuple[dict, list[Cell]]:
    """Read `sweep_summary.json` plus every run's `summary.json`.

    Falls back to scanning `runs/` when the top-level summary is absent, so a
    directory assembled from several partial sweeps still renders.
    """
    out_root = Path(out_root)
    runs_dir = out_root / "runs"
    if not runs_dir.is_dir():
        raise FileNotFoundError(
            f"no EGT runs under {out_root} — run a sweep first "
            "(`python -m pd_runner.egt.pipeline`)"
        )

    summary_path = out_root / "sweep_summary.json"
    sweep = json.loads(summary_path.read_text()) if summary_path.exists() else {}

    cells: list[Cell] = []
    for run_dir in sorted(p for p in runs_dir.iterdir() if p.is_dir()):
        payload_path = run_dir / "summary.json"
        if not payload_path.exists():
            continue
        d = json.loads(payload_path.read_text())
        cells.append(Cell(
            run=d["run"],
            zoo=d.get("zoo") or "unknown",
            t=float(d["t"]) if d.get("t") is not None else 1.0,
            alpha=float(d["alpha"]) if d.get("alpha") is not None else 0.0,
            fingerprint=d.get("fingerprint", ""),
            n_types=d.get("n_types", 0),
            bots=tuple(d.get("bots", ())),
            excluded_bots=tuple(d.get("excluded_bots", ())),
            is_fully_proven=bool(d.get("is_fully_proven", True)),
            grid_points=tuple((float(a), float(b)) for a, b in d.get("grid_points", ())),
            ok=bool(d.get("ok", True)),
            stages=d.get("stages", {}),
            run_dir=run_dir,
        ))

    if not cells:
        raise FileNotFoundError(f"no run summaries under {runs_dir}")
    return sweep, cells


def _cell_index(cells: Sequence[Cell]) -> dict[tuple[str, str], Cell]:
    """Map EVERY grid point to the cell that covers it.

    Dedup means one run can own several points; without this the picker would
    have holes wherever a point was folded into an earlier matrix.
    """
    index: dict[tuple[str, str], Cell] = {}
    for cell in cells:
        points = cell.grid_points or ((cell.t, cell.alpha),)
        for t, alpha in points:
            index[(_key(t), _key(alpha))] = cell
    return index


def _key(x: float) -> str:
    """Canonical string for a dial value, so JS and Python agree on it."""
    return f"{x:g}"


# --------------------------------------------------------------------------
# Chart primitives (inline SVG, no dependencies)
# --------------------------------------------------------------------------


def _fmt(value, dash: str = "—") -> str:
    if value is None:
        return dash
    if isinstance(value, float):
        return f"{value:g}"
    return str(value)


def _line_chart(
    series: list[tuple[str, list[tuple[float, float]], str]],
    width: int = 720,
    height: int = 300,
    y_label: str = "",
    x_label: str = "transparency t",
    y_max: float | None = None,
) -> str:
    """Line chart over the t axis, x running 1.0 (left) → 0.0 (right).

    Direction matches every chart in the tau report: the reader moves
    left-to-right in the direction of degrading signal. Series are direct-
    labelled at their right endpoint — mandatory here, since the palette's
    worst adjacent pair is in the 6-8 CVD band.
    """
    pad_l, pad_r, pad_t, pad_b = 54, 132, 14, 44
    plot_w, plot_h = width - pad_l - pad_r, height - pad_t - pad_b

    all_y = [y for _, pts, _ in series for _, y in pts]
    top = y_max if y_max is not None else (max(all_y) if all_y else 1.0)
    top = top if top > 0 else 1.0

    def sx(x: float) -> float:
        return pad_l + (1.0 - x) * plot_w

    def sy(y: float) -> float:
        return pad_t + (1.0 - y / top) * plot_h

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']

    # Horizontal gridlines — solid hairlines, one shade off the surface.
    for i in range(5):
        frac = i / 4
        y = pad_t + (1 - frac) * plot_h
        parts.append(
            f'<line class="grid" x1="{pad_l}" y1="{y:.1f}" '
            f'x2="{pad_l + plot_w}" y2="{y:.1f}"/>'
        )
        parts.append(
            f'<text class="tick end" x="{pad_l - 8}" y="{y + 4:.1f}">'
            f"{_fmt(round(top * frac, 2))}</text>"
        )

    # x ticks at the sampled transparencies.
    xs = sorted({x for _, pts, _ in series for x, _ in pts}, reverse=True)
    for x in xs:
        parts.append(
            f'<text class="tick mid" x="{sx(x):.1f}" y="{pad_t + plot_h + 18}">'
            f"{x:g}</text>"
        )
    parts.append(
        f'<text class="axis mid" x="{pad_l + plot_w / 2:.1f}" '
        f'y="{height - 6}">{html.escape(x_label)} — full transparency at left</text>'
    )
    if y_label:
        parts.append(
            f'<text class="axis" x="4" y="{pad_t + 4}">{html.escape(y_label)}</text>'
        )

    for label, points, colour in series:
        if not points:
            continue
        ordered = sorted(points, key=lambda p: -p[0])
        d = " ".join(
            ("M" if i == 0 else "L") + f"{sx(x):.1f} {sy(y):.1f}"
            for i, (x, y) in enumerate(ordered)
        )
        parts.append(f'<path class="line" d="{d}" stroke="{colour}"/>')
        for x, y in ordered:
            # 2px surface ring so overlapping markers stay separable.
            parts.append(
                f'<circle cx="{sx(x):.1f}" cy="{sy(y):.1f}" r="4" '
                f'fill="{colour}" stroke="var(--bg)" stroke-width="2"/>'
            )
        lx, ly = ordered[-1]
        parts.append(
            f'<text class="legend" x="{sx(lx) + 10:.1f}" y="{sy(ly) + 4:.1f}" '
            f'fill="{colour}">{html.escape(label)}</text>'
        )

    parts.append("</svg>")
    return "".join(parts)


def _phase_grid(
    cells: Sequence[Cell],
    ts: Sequence[float],
    alphas: Sequence[float],
    index: dict[tuple[str, str], Cell],
    metric: str,
    label: str,
) -> str:
    """The (t, α) plane as a heatmap — one hue, light→dark, for magnitude.

    Every tile carries its value as text, which is what discharges the
    palette's contrast obligation: the colour is redundant with the number.
    """
    getter = {
        "n_extreme_ne": lambda c: c.n_extreme_ne,
        "stable_faces": lambda c: c.stable_faces,
        "n_sccs": lambda c: c.n_sccs,
        "edges_strict": lambda c: c.edges_strict,
    }[metric]

    values = [v for c in cells if (v := getter(c)) is not None]
    if not values:
        return '<p class="note">No data for this metric — the stage did not run.</p>'
    lo, hi = min(values), max(values)
    span = (hi - lo) or 1

    cw, ch = 74, 34
    pad_l, pad_t = 56, 34
    width = pad_l + cw * len(ts) + 8
    height = pad_t + ch * len(alphas) + 30

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    for j, t in enumerate(ts):
        parts.append(
            f'<text class="tick mid" x="{pad_l + cw * j + cw / 2:.1f}" '
            f'y="{pad_t - 10}">t={t:g}</text>'
        )
    for i, alpha in enumerate(alphas):
        parts.append(
            f'<text class="tick end" x="{pad_l - 8}" '
            f'y="{pad_t + ch * i + ch / 2 + 4:.1f}">α={alpha:g}</text>'
        )

    for i, alpha in enumerate(alphas):
        for j, t in enumerate(ts):
            cell = index.get((_key(t), _key(alpha)))
            x, y = pad_l + cw * j, pad_t + ch * i
            value = getter(cell) if cell else None
            if value is None:
                parts.append(
                    f'<rect x="{x + 1}" y="{y + 1}" width="{cw - 2}" height="{ch - 2}" '
                    f'rx="4" fill="var(--panel)" stroke="var(--border)"/>'
                    f'<text class="tick mid" x="{x + cw / 2:.1f}" '
                    f'y="{y + ch / 2 + 4:.1f}">—</text>'
                )
                continue
            # Single hue, light→dark. 0.12→0.92 keeps text legible at both ends.
            frac = (value - lo) / span
            fill = f"color-mix(in oklab, {_C_BLUE} {12 + frac * 80:.0f}%, var(--bg))"
            ink = "#fff" if frac > 0.55 else "var(--fg)"
            parts.append(
                f'<rect x="{x + 1}" y="{y + 1}" width="{cw - 2}" height="{ch - 2}" '
                f'rx="4" fill="{fill}"/>'
                f'<text class="cellnum mid" x="{x + cw / 2:.1f}" '
                f'y="{y + ch / 2 + 4:.1f}" fill="{ink}">{value}</text>'
            )

    parts.append(
        f'<text class="axis" x="{pad_l}" y="{height - 8}">'
        f"{html.escape(label)} · darker = higher (range {lo}–{hi})</text>"
    )
    parts.append("</svg>")
    return "".join(parts)


def _bar_row(entries: list[tuple[str, int, str]], width: int = 720) -> str:
    """Horizontal bars with the label and value outside the mark.

    Labels never sit inside the bar, so a short bar can't clip its own text.
    """
    if not entries:
        return '<p class="note">Nothing to show.</p>'
    total = max(v for _, v, _ in entries) or 1
    row_h, pad_l, pad_r = 26, 176, 56
    plot_w = width - pad_l - pad_r
    height = row_h * len(entries) + 8

    parts = [f'<svg viewBox="0 0 {width} {height}" class="chart" role="img">']
    for i, (label, value, colour) in enumerate(entries):
        y = i * row_h + 4
        w = (value / total) * plot_w
        parts.append(
            f'<text class="tick end" x="{pad_l - 10}" y="{y + 15}">'
            f"{html.escape(label)}</text>"
            f'<rect x="{pad_l}" y="{y + 4}" width="{max(w, 1):.1f}" height="14" '
            f'rx="4" fill="{colour}"/>'
            f'<text class="cellnum" x="{pad_l + max(w, 1) + 8:.1f}" y="{y + 15}">'
            f"{value}</text>"
        )
    parts.append("</svg>")
    return "".join(parts)


# --------------------------------------------------------------------------
# Per-cell panels
# --------------------------------------------------------------------------


def _inline_svg(path: Path, max_bytes: int = 400_000) -> str:
    """Embed a matplotlib SVG in the page.

    Strips the XML prolog and DOCTYPE (illegal mid-document) and drops any
    fixed width/height so the figure scales to the panel. Falls back to a link
    if the file is implausibly large — a page with a dozen embedded figures
    should not become unopenable.
    """
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError:
        return '<p class="note missing">Figure could not be read.</p>'
    if len(raw) > max_bytes:
        return (
            f'<p class="note">Figure is {len(raw) // 1024} kB — too large to '
            f"inline; open <code>{html.escape(path.name)}</code> from the "
            f"artefact links below.</p>"
        )
    start = raw.find("<svg")
    if start < 0:
        return '<p class="note missing">Figure is not an SVG.</p>'
    svg = raw[start:]
    # matplotlib writes width="460.8pt" height="345.6pt"; the viewBox carries
    # the aspect ratio, so dropping both lets CSS size it responsively.
    svg = re.sub(r'\s(width|height)="[\d.]+pt"', "", svg, count=2)
    return svg


def _stat_tiles(cell: Cell) -> str:
    tiles = [
        (cell.n_types, "types analysed"),
        (_fmt(cell.n_pure_ess), "pure ESS"),
        (_fmt(cell.n_extreme_ne), "extreme NE"),
        (_fmt(cell.n_components), "Nash components"),
        (_fmt(cell.stable_faces), "stable faces"),
        (_fmt(cell.n_sccs), "SCCs"),
    ]
    return '<ul class="stats">' + "".join(
        f"<li><b>{v}</b><span>{html.escape(s)}</span></li>" for v, s in tiles
    ) + "</ul>"


def _faces_section(cell: Cell) -> str:
    by_class = cell.faces_by_class
    if not by_class:
        return '<p class="note">The faces stage did not run for this cell.</p>'
    order = ["asymp_stable", "asymp_stable_invadable", "saddle", "unstable",
             "non_hyperbolic", "non_interior", "singular"]
    colour = {
        "asymp_stable": _C_BLUE,
        "asymp_stable_invadable": _C_BLUE,
        "saddle": _EXPLOIT,
    }
    entries = [
        (k.replace("_", " "), by_class[k], colour.get(k, _D_GREY))
        for k in order if by_class.get(k)
    ]
    entries += [
        (k.replace("_", " "), v, _D_GREY)
        for k, v in by_class.items() if k not in order and v
    ]
    trunc = (
        '<p class="banner warn">Enumeration was TRUNCATED — larger faces were '
        "not examined, so the absence of a stable equilibrium among them is "
        "unproven, not evidence.</p>"
        if not cell.enumeration_complete else ""
    )
    rows = "".join(
        f"<tr><td>{html.escape(k.replace('_', ' '))}</td>"
        f'<td class="num">{v}</td></tr>'
        for k, v in sorted(by_class.items(), key=lambda kv: -kv[1])
    )
    return (
        f"{trunc}"
        f'<div class="panel">{_bar_row(entries)}</div>'
        f'<details><summary>Table view — face classes</summary>'
        f'<table class="fam"><thead><tr><th>class</th><th class="num">count</th>'
        f"</tr></thead><tbody>{rows}</tbody></table></details>"
    )


def _cell_panel(cell: Cell, artefact_base: str, repeat_conditional: bool = True) -> str:
    """Everything shown for one analysed matrix.

    `repeat_conditional=False` suppresses the per-cell "conditional" banner —
    used when EVERY matrix in the sweep is conditional, so the page-level
    banner already said it once and repeating it on all twelve panels is
    noise that trains the reader to skip banners.
    """
    warnings = []
    if not cell.is_fully_proven and repeat_conditional:
        warnings.append(
            '<p class="banner warn"><b>Conditional.</b> Some cells of this '
            "matrix are stipulated rather than proven by the Lean library; "
            "every number below rests on them.</p>"
        )
    if cell.excluded_bots:
        warnings.append(
            f'<p class="banner warn"><b>Excluded:</b> '
            f"{html.escape(', '.join(cell.excluded_bots))} — dropped by the "
            "non-termination policy (a proven <code>none</code> outcome has no "
            "defensible payoff).</p>"
        )
    if cell.failed_stages():
        warnings.append(
            f'<p class="banner warn"><b>Failed stages:</b> '
            f"{html.escape(', '.join(cell.failed_stages()))}. Their numbers are "
            "absent below, not zero.</p>"
        )
    if cell.cross_check_performed is False:
        warnings.append(
            '<p class="banner note-banner">The pygambit/lrsnash cross-check '
            "was <b>skipped</b> (lrslib not installed): the Nash figures come "
            "from one solver, unverified against a second.</p>"
        )

    shared = ", ".join(f"(t={t:g}, α={a:g})" for t, a in cell.grid_points)
    dedup = (
        f'<p class="note">This matrix covers {len(cell.grid_points)} grid '
        f"points: {html.escape(shared)}. They share one analysis because their "
        f"action-pair cells are identical.</p>"
        if len(cell.grid_points) > 1 else ""
    )

    invasion = (
        f'<ul class="stats"><li><b>{_fmt(cell.edges_strict)}</b>'
        f"<span>strict edges</span></li>"
        f"<li><b>{_fmt(cell.n_sccs)}</b><span>SCCs</span></li>"
        f"<li><b>{_fmt(cell.n_cycles)}</b><span>simple cycles</span></li></ul>"
    )

    graph_svg = cell.run_dir / "invasion" / "graph.svg"
    figure = (
        # Inline the SVG so the figure IS the page — no broken-image risk under
        # file://, and it inherits the reader's light/dark surface.
        f'<div class="panel figure">{_inline_svg(graph_svg)}</div>'
        if graph_svg.exists() else
        '<p class="note missing">Figures were not rendered for this run '
        "(<code>--no-render</code>, or the invasion stage failed).</p>"
    )

    return (
        f"{''.join(warnings)}"
        f"{dedup}"
        f"{_stat_tiles(cell)}"
        f"<h3>Invasion graph</h3>{invasion}{figure}"
        f"<h3>Face equilibria</h3>{_faces_section(cell)}"
        f"<h3>Artefacts</h3>{_artefact_links(cell, artefact_base)}"
    )


def _artefact_links(cell: Cell, artefact_base: str) -> str:
    """Link the artefacts that EXIST, file by file.

    Deliberately not a link to the run directory: the API serves these through
    `StaticFiles`, which does not do directory listings, so a bare directory
    link would 404. Linking real files keeps the page honest under both
    `file://` and the server.
    """
    candidates = [
        ("ess/report.md", "ESS report"),
        ("ess/ess_summary.csv", "ESS summary (CSV)"),
        ("ess/payoff_matrix_numeric.csv", "payoff matrix (CSV)"),
        ("invasion/report.md", "invasion report"),
        ("invasion/graph.svg", "invasion graph (SVG)"),
        ("invasion/condensation.svg", "condensation (SVG)"),
        ("invasion/graph.gexf", "invasion graph (GEXF)"),
        ("faces/summary.md", "faces summary"),
        ("faces/face_equilibria.csv", "face equilibria (CSV)"),
    ]
    links = [
        f'<a href="{artefact_base}/{cell.run}/{rel}">{html.escape(label)}</a>'
        for rel, label in candidates
        if (cell.run_dir / rel).exists()
    ]
    # The Nash stage nests its outputs under a per-run timestamp directory.
    nash_runs = sorted((cell.run_dir / "nash" / "runs").glob("*/equilibria.jsonl"))
    if nash_runs:
        rel = nash_runs[-1].relative_to(cell.run_dir)
        links.append(
            f'<a href="{artefact_base}/{cell.run}/{rel}">equilibria (JSONL)</a>'
        )
        summary = nash_runs[-1].parent / "equilibria_summary.md"
        if summary.exists():
            rel = summary.relative_to(cell.run_dir)
            links.append(
                f'<a href="{artefact_base}/{cell.run}/{rel}">Nash summary</a>'
            )
    if not links:
        return '<p class="note missing">No artefacts found for this matrix.</p>'
    return (
        f'<p class="note">{" · ".join(links)}<br>Directory: '
        f"<code>{html.escape(cell.run)}/</code> "
        f"(fingerprint <code>{html.escape(cell.fingerprint)}</code>).</p>"
    )


# --------------------------------------------------------------------------
# The page
# --------------------------------------------------------------------------


_CSS = """
:root { color-scheme: light dark; --fg:#1a1a1a; --muted:#666; --bg:#fff;
        --panel:#f7f7f8; --border:#e2e2e5; --c:#0072b2; }
@media (prefers-color-scheme: dark) {
  :root { --fg:#e8e8ea; --muted:#a0a0a8; --bg:#16161a; --panel:#1f1f25;
          --border:#33333c; }
}
* { box-sizing: border-box; }
body { margin:0; padding:2.5rem 1.5rem 4rem; background:var(--bg); color:var(--fg);
       font:15px/1.6 -apple-system,BlinkMacSystemFont,"Segoe UI",Helvetica,sans-serif; }
main { max-width: 880px; margin: 0 auto; }
h1 { font-size:1.6rem; margin:0 0 .3rem; letter-spacing:-.01em; }
h2 { font-size:1.1rem; margin:2.5rem 0 .4rem; letter-spacing:-.01em; }
h3 { font-size:.95rem; margin:1.6rem 0 .3rem; color:var(--fg); }
.sub { color:var(--muted); margin:0 0 1.4rem; }
.note { color:var(--muted); font-size:.9rem; margin:.3rem 0 1rem; }
.panel { background:var(--panel); border:1px solid var(--border);
         border-radius:10px; padding:1rem; margin:.6rem 0 0; overflow-x:auto; }
.chart { width:100%; height:auto; display:block; }
.grid { stroke:var(--border); stroke-width:1; }
.line { fill:none; stroke-width:2; stroke-linejoin:round; stroke-linecap:round; }
.tick { fill:var(--muted); font-size:11px; }
.legend { font-size:11px; font-weight:600; }
.axis { fill:var(--muted); font-size:11px; }
.cellnum { fill:var(--fg); font-size:11px; font-weight:600; }
.end { text-anchor:end; } .mid { text-anchor:middle; }
.stats { display:flex; flex-wrap:wrap; gap:.6rem; margin:1rem 0 0; padding:0;
         list-style:none; }
.stats li { background:var(--panel); border:1px solid var(--border);
            border-radius:8px; padding:.6rem .85rem; min-width:118px; }
.stats b { display:block; font-size:1.25rem; letter-spacing:-.02em; }
.stats span { color:var(--muted); font-size:.8rem; }
.picker { display:flex; align-items:center; gap:.8rem; flex-wrap:wrap;
          background:var(--panel); border:1px solid var(--border);
          border-radius:10px; padding:.7rem 1rem; margin:.6rem 0 0;
          position:sticky; top:0; z-index:5; }
.picker label { color:var(--muted); font-size:.85rem; min-width:8.5rem; }
.picker input[type="range"] { flex:1; min-width:170px; accent-color:var(--c); }
.pill { display:inline-block; background:var(--c); color:#fff; font-size:.72rem;
        font-weight:600; padding:.15rem .5rem; border-radius:999px;
        min-width:5.4rem; text-align:center; }
code { background:var(--panel); padding:.1rem .3rem; border-radius:4px; font-size:.9em; }
a { color:var(--c); }
.banner { border-radius:8px; padding:.7rem .9rem; margin:1rem 0 0;
          font-size:.88rem; line-height:1.5; border:1px solid; }
.banner.warn { background:rgba(213,94,0,.10); border-color:rgba(213,94,0,.55); }
.banner.ok { background:rgba(0,158,115,.10); border-color:rgba(0,158,115,.5); }
.banner.note-banner { background:var(--panel); border-color:var(--border);
                      color:var(--muted); }
table.fam { border-collapse:collapse; font-size:.82rem; width:100%; margin:.5rem 0 0; }
table.fam th, table.fam td { border-bottom:1px solid var(--border);
                             padding:6px 10px; text-align:left; }
table.fam th { color:var(--muted); font-weight:500; }
table.fam td.num, table.fam th.num { text-align:right; font-variant-numeric:tabular-nums; }
details { margin:.7rem 0 0; }
summary { cursor:pointer; color:var(--muted); font-size:.85rem; }
.missing { color:var(--muted); font-style:italic; }
/* Embedded matplotlib figures: scale to the panel, keep aspect from viewBox. */
.figure svg { width:100%; height:auto; display:block; max-width:100%; }
/* matplotlib writes an opaque white page rect; in dark mode that would be a
   glaring white slab, so drop the figure's own background and let the panel
   show through. The plotted marks carry their own colours. */
@media (prefers-color-scheme: dark) {
  .figure svg { filter: invert(1) hue-rotate(180deg); }
}
"""


def build_report(out_root: Path, artefact_base: str = "runs") -> str:
    """Render the whole page for the sweep under `out_root`."""
    sweep, cells = load_sweep(out_root)
    index = _cell_index(cells)

    ts = sorted({t for (t, _) in (p for c in cells for p in
                                  (c.grid_points or ((c.t, c.alpha),)))}, reverse=True)
    alphas = sorted({a for (_, a) in (p for c in cells for p in
                                      (c.grid_points or ((c.t, c.alpha),)))})

    zoo = cells[0].zoo
    n_points = sweep.get("n_grid_points", sum(
        len(c.grid_points) or 1 for c in cells))
    saved = sweep.get("dedup_saved", n_points - len(cells))

    # --- cross-cell trend charts (one line per α, x = t) ------------------
    def trend(metric) -> list[tuple[str, list[tuple[float, float]], str]]:
        out = []
        for i, alpha in enumerate(alphas):
            pts = []
            for t in ts:
                cell = index.get((_key(t), _key(alpha)))
                if cell is None:
                    continue
                v = metric(cell)
                if v is not None:
                    pts.append((t, float(v)))
            if pts:
                out.append((f"α={alpha:g}", pts,
                            _SERIES_COLORS[i % len(_SERIES_COLORS)]))
        return out

    ne_series = trend(lambda c: c.n_extreme_ne)
    scc_series = trend(lambda c: c.n_sccs)
    stable_series = trend(lambda c: c.stable_faces)

    def chart_or_note(series, y_label) -> str:
        if not series:
            return ('<p class="note missing">This stage did not run in the '
                    "sweep, so there is nothing to plot.</p>")
        return f'<div class="panel">{_line_chart(series, y_label=y_label)}</div>'

    # A single-t sweep has no line to draw; say so rather than render a dot.
    single_t = len(ts) < 2
    if single_t:
        trend_note = ('<p class="note missing">The sweep has a single '
                      "transparency, so there is no trend to plot — use the "
                      "picker below to read the cell.</p>")
        ne_chart = scc_chart = stable_chart = trend_note
    else:
        ne_chart = chart_or_note(ne_series, "extreme NE")
        scc_chart = chart_or_note(scc_series, "SCCs")
        stable_chart = chart_or_note(stable_series, "stable faces")

    # --- the (t, α) picker ------------------------------------------------
    # When every matrix is conditional the page-level banner covers it, so the
    # per-cell repeat is suppressed (see `_cell_panel`).
    all_conditional = all(not c.is_fully_proven for c in cells)
    panels = []
    for t in ts:
        for alpha in alphas:
            cell = index.get((_key(t), _key(alpha)))
            body = (
                _cell_panel(cell, artefact_base,
                            repeat_conditional=not all_conditional)
                if cell is not None else
                '<p class="note missing">This grid point was not analysed in '
                "this sweep.</p>"
            )
            panels.append(
                f'<div class="swap-view" data-t="{_key(t)}" '
                f'data-alpha="{_key(alpha)}" hidden>{body}</div>'
            )

    ts_js = json.dumps([_key(t) for t in ts])
    alphas_js = json.dumps([_key(a) for a in alphas])

    picker_script = (
        "<script>(function(){\n"
        f"  var ts = {ts_js}, alphas = {alphas_js};\n"
        '  var tS = document.getElementById("t-slider");\n'
        '  var aS = document.getElementById("a-slider");\n'
        '  var views = document.querySelectorAll(".swap-view");\n'
        "  function show(){\n"
        "    var t = ts[+tS.value], a = alphas[+aS.value];\n"
        "    views.forEach(function(el){\n"
        "      el.hidden = el.dataset.t !== t || el.dataset.alpha !== a;\n"
        "    });\n"
        '    document.getElementById("t-out").textContent = "t = " + t;\n'
        '    document.getElementById("a-out").textContent = "\\u03b1 = " + a;\n'
        "  }\n"
        '  tS.addEventListener("input", show);\n'
        '  aS.addEventListener("input", show);\n'
        "  show();\n"
        "})();</script>"
    )

    # --- provenance -------------------------------------------------------
    conditional = [c for c in cells if not c.is_fully_proven]
    failed = [c for c in cells if not c.ok]
    banners = []
    if conditional:
        banners.append(
            f'<p class="banner warn"><b>{len(conditional)} of {len(cells)}</b> '
            "analysed matrices rest on stipulated (unproven) cells. Those "
            "results are conditional — say so when reporting them.</p>"
        )
    if failed:
        names = ", ".join(c.run for c in failed[:3])
        banners.append(
            f'<p class="banner warn"><b>{len(failed)}</b> matrices had a failing '
            f"stage ({html.escape(names)}{'…' if len(failed) > 3 else ''}). "
            "Missing numbers below are absent, not zero.</p>"
        )
    if not conditional and not failed:
        banners.append(
            '<p class="banner ok">Every analysed matrix completed all its '
            "stages, and none rests on a stipulated cell.</p>"
        )

    rows = "".join(
        f"<tr><td>t={c.t:g}, α={c.alpha:g}</td>"
        f'<td class="num">{len(c.grid_points) or 1}</td>'
        f'<td class="num">{_fmt(c.n_pure_ess)}</td>'
        f'<td class="num">{_fmt(c.edges_strict)}</td>'
        f'<td class="num">{_fmt(c.n_sccs)}</td>'
        f'<td class="num">{_fmt(c.stable_faces)}</td>'
        f'<td class="num">{_fmt(c.n_extreme_ne)}</td>'
        f'<td class="num">{_fmt(c.n_components)}</td></tr>'
        for c in sorted(cells, key=lambda c: (-c.t, c.alpha))
    )

    # The headline heatmap uses the richest metric the sweep actually has, so
    # a sweep run without the (expensive) nash stage still gets a phase plane
    # instead of an empty panel.
    _HEAT_METRICS = [
        ("n_extreme_ne", "extreme Nash equilibria", lambda c: c.n_extreme_ne),
        ("stable_faces", "asymptotically stable faces", lambda c: c.stable_faces),
        ("n_sccs", "strongly connected components", lambda c: c.n_sccs),
        ("edges_strict", "strict invasion edges", lambda c: c.edges_strict),
    ]
    heat_metric, heat_label, _ = next(
        (m for m in _HEAT_METRICS if any(m[2](c) is not None for c in cells)),
        _HEAT_METRICS[0],
    )
    heat = _phase_grid(cells, ts, alphas, index, heat_metric, heat_label)

    return f"""<title>EGT — evolutionary analysis ({html.escape(zoo)})</title>
<style>{_CSS}</style>
<main>
<h1>Evolutionary analysis over the (t, α) plane</h1>
<p class="sub">Which bots survive in a <em>population</em> of bots ·
zoo <b>{html.escape(zoo)}</b> · {cells[0].n_types} types ·
{len(cells)} distinct matrices from {n_points} grid points</p>

<ul class="stats">
  <li><b>{len(cells)}</b><span>matrices analysed</span></li>
  <li><b>{n_points}</b><span>grid points</span></li>
  <li><b>{saved}</b><span>saved by dedup</span></li>
  <li><b>{_fmt(sweep.get("seconds"))}</b><span>seconds</span></li>
</ul>
{"".join(banners)}

<p class="note">Each grid point is a tau tournament at transparency <code>t</code>
and caution threshold <code>α</code>, converted to a payoff matrix and pushed
through four analyses. Points whose action-pair cells coincide are analysed
once — that is what <b>saved by dedup</b> counts.</p>

<h2>1 · The (t, α) phase plane</h2>
<p class="note">{html.escape(heat_label[0].upper() + heat_label[1:])} across the
plane. One hue, light→dark; every tile carries its value, so the colour is
redundant with the number rather than the only way to read it. A dash means the
point was not analysed.</p>
<div class="panel">{heat}</div>

<h2>2 · Nash equilibria vs transparency</h2>
<p class="note">How the equilibrium count moves as the signal degrades, one line
per caution threshold. Lines are labelled at their right endpoint.</p>
{ne_chart}

<h2>3 · Population structure vs transparency</h2>
<p class="note">Strongly connected components of the strict invasion graph. More
SCCs means a more fragmented population — fewer mutually-invadable clusters.</p>
{scc_chart}

<h2>4 · Stable faces vs transparency</h2>
<p class="note">Faces classified <code>asymp_stable</code> or
<code>asymp_stable_invadable</code>: mixed populations that hold together at
least within their own support.</p>
{stable_chart}

<h2>5 · Pick a cell</h2>
<p class="note">Everything below is for ONE analysed matrix. Move either slider
to change which. Grid points that share a matrix show the same panel — the
picker resolves them, so it never lands on a hole.</p>
<div class="picker">
  <label for="t-slider">transparency t</label>
  <input id="t-slider" type="range" min="0" max="{max(len(ts) - 1, 0)}"
         step="1" value="0" list="t-marks">
  <span class="pill" id="t-out"></span>
</div>
<div class="picker">
  <label for="a-slider">caution threshold α</label>
  <input id="a-slider" type="range" min="0" max="{max(len(alphas) - 1, 0)}"
         step="1" value="0" list="a-marks">
  <span class="pill" id="a-out"></span>
</div>
{"".join(panels)}

<h2>6 · Every matrix, side by side</h2>
<p class="note">The table view — every number on this page is reachable here
without hovering or dragging. <code>—</code> means the stage did not run or
failed; it never means zero.</p>
<div class="panel">
<table class="fam">
<thead><tr>
  <th>cell</th><th class="num">pts</th><th class="num">ESS</th>
  <th class="num">edges</th><th class="num">SCCs</th>
  <th class="num">stable faces</th><th class="num">extreme NE</th>
  <th class="num">components</th>
</tr></thead>
<tbody>{rows}</tbody>
</table>
</div>

<h2>Provenance</h2>
<p class="note">Payoffs use the donation convention
<code>(D,C)=b, (C,C)=b−c, (D,D)=0, (C,D)=−c</code> with <code>b&gt;c&gt;0</code>.
Every stage writes an <code>assumptions.json</code> next to its outputs
recording the conventions it used; nothing on this page is imputed. Full
artefacts live under <code>{html.escape(artefact_base)}/</code>.</p>
</main>
{picker_script}
"""


def main() -> None:
    import argparse
    import subprocess

    from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

    p = argparse.ArgumentParser(description="Build the EGT HTML report.")
    p.add_argument("--out-root", type=Path, default=DEFAULT_OUT_ROOT,
                   help="sweep directory to read (must contain runs/)")
    p.add_argument("--output", type=Path, default=None,
                   help="where to write the page (default: <out-root>/report.html)")
    p.add_argument("--open", action="store_true", help="open in the browser")
    args = p.parse_args()

    output = args.output or (args.out_root / "report.html")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(build_report(args.out_root), encoding="utf-8")
    print(f"wrote {output}")
    if args.open:
        subprocess.run(["open", str(output)], check=False)


if __name__ == "__main__":
    main()

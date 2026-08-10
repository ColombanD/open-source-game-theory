"""HTML report over a finished EGT sweep.

The counterpart to `tau/report.py`, and deliberately built the same way: one
self-contained page, inline SVG, no external assets, light/dark from the same
CSS-variable palette. What differs is the input — the tau report computes its
own tournaments, whereas this one READS a sweep that already ran, because the
four analysis stages cost minutes and their artefacts are the record.

Layout: §1 the sweep as one table, then ONE SECTION PER ANALYSIS — §2 ESS,
§3 invasion, §4 faces, §5 Nash — then provenance and artefacts. Each analysis
section holds its own cross-cell trend AND its per-cell view, rather than
splitting those across the page: a reader following "how do face equilibria
behave" should not have to jump between a chart near the top and a grid near
the bottom.

The sections run strongest claim to weakest: a single unbeatable type (ESS),
who displaces whom (invasion), whether a mixture holds (faces), what is
rational at all (Nash).

Per-cell views use two presentations, chosen by how big the answer is: a
**(t, α) grid** where it reads at a glance (ESS names, face-class counts), and
a **(t, α) dropdown** where it is a figure or a table (invasion graph, Nash
components). Dropdown views are all pre-rendered and toggled by `data-kind` +
`data-t`/`data-alpha`, so there is no server round-trip and the page works
from `file://`.

Grid points that shared a matrix (dedup) resolve to the same view, so a
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
# Exact-rational display
# --------------------------------------------------------------------------


def _fmt_rational(value: str) -> str:
    """Display an exact `numerator/denominator` string, dropping a `/1` tail.

    The Nash stage computes in `fractions.Fraction` and serialises every value
    as `n/d`, which is right for the artefacts: `43/147` has no terminating
    decimal, and the whole point of exact arithmetic is that the equilibrium
    verifies rather than nearly-verifies.

    But `2/1` is just `2`. On matrices whose equilibria are all pure the entire
    column reads `2/1`, `0/1`, `1/1`, where the denominators carry no
    information and make the real fractions harder to spot. Rendering an
    integer as an integer loses nothing — it is still exact.

    Only the DISPLAY changes; the on-disk artefacts keep `n/d` verbatim,
    because their schema is pinned and machine-read.
    """
    if not isinstance(value, str):
        return str(value)
    numerator, sep, denominator = value.partition("/")
    if sep and denominator.strip() == "1":
        return numerator.strip()
    return value


def _fmt_range(values: Sequence[str]) -> str:
    """One formatted value, or `lo…hi` when a component spans several."""
    if not values:
        return "—"
    if len(values) == 1:
        return _fmt_rational(values[0])
    return f"{_fmt_rational(values[0])}…{_fmt_rational(values[-1])}"


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

    # ---- artefact readers -------------------------------------------------
    # The stage summaries carry COUNTS; the deep-dive sections need the names
    # and groupings behind them, which live in the stage artefacts on disk.

    def ess_bots(self) -> list[str] | None:
        """Names of the types that ARE a pure ESS, or None if ii.a is absent.

        `None` and `[]` mean different things and must not be conflated:
        `None` = the stage never ran, `[]` = it ran and found none.
        """
        path = self.run_dir / "ess" / "ess_summary.csv"
        if not path.exists():
            return None
        import csv

        with path.open(newline="") as fh:
            return [
                row["type"] for row in csv.DictReader(fh)
                if row.get("is_ESS", "").strip().lower() == "true"
            ]

    def invasion_svg(self) -> Path | None:
        path = self.run_dir / "invasion" / "graph.svg"
        return path if path.exists() else None

    def basins(self) -> dict | None:
        """Stage (iii) `basins.json`, or None if the stage did not run."""
        path = self.run_dir / "replicator" / "basins.json"
        if not path.exists():
            return None
        return json.loads(path.read_text())

    def moran_points(self) -> list[dict] | None:
        """Stage (iv) `(M, beta)` points, or None if the stage did not run."""
        path = self.run_dir / "moran" / "stationary.json"
        if not path.exists():
            return None
        return json.loads(path.read_text()).get("points", [])

    def nash_components(self) -> list[dict] | None:
        """Per-component rollup: size, payoff, cooperation rate, bots involved.

        Returns None when the Nash stage is absent. Payoff and cooperation
        rate are constant within a component on every matrix seen so far, but
        the range is computed rather than assumed — a component that ever
        spans several values must say so instead of showing one silently.
        """
        runs = sorted((self.run_dir / "nash" / "runs").glob("*/equilibria.jsonl"))
        if not runs:
            return None
        equilibria = [json.loads(line) for line in runs[-1].read_text().splitlines() if line.strip()]
        if not equilibria:
            return []

        grouped: dict[int, list[dict]] = {}
        for eq in equilibria:
            grouped.setdefault(eq.get("component_id", -1), []).append(eq)

        out = []
        for cid, members in sorted(grouped.items()):
            bots = sorted({
                b for m in members
                for b in (m.get("support_row_names", []) + m.get("support_col_names", []))
            })
            payoffs = sorted({m.get("u_rational") for m in members})
            coops = sorted({m.get("cooperation_rate_rational") for m in members})
            out.append({
                "id": cid,
                "n_equilibria": len(members),
                # Formatted for display at construction so both ends of a
                # range get the same treatment (see `_fmt_rational`).
                "payoff": _fmt_range(payoffs),
                "coop_rate": _fmt_range(coops),
                "bots": bots,
                "has_symmetric": any(m.get("classification") == "symmetric" for m in members),
                "touches_suspect": any(m.get("touches_suspect_cell") for m in members),
            })
        return out


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


def _artefacts_section(cells: Sequence[Cell], artefact_base: str) -> str:
    """The closing section: per-matrix warnings and links to every artefact.

    This is where the per-cell caveats live now that the picker is gone —
    excluded bots, failed stages, a skipped Nash cross-check. They are
    matrix-specific, so they cannot be collapsed into the page-level banner;
    dropping them would hide that a number is missing rather than zero.
    """
    blocks = []
    for cell in sorted(cells, key=lambda c: (-c.t, c.alpha)):
        warnings = []
        if cell.excluded_bots:
            warnings.append(
                f'<p class="banner warn"><b>Excluded:</b> '
                f"{html.escape(', '.join(cell.excluded_bots))} — dropped by the "
                "non-termination policy (a proven <code>none</code> outcome has "
                "no defensible payoff).</p>"
            )
        if cell.failed_stages():
            warnings.append(
                f'<p class="banner warn"><b>Failed stages:</b> '
                f"{html.escape(', '.join(cell.failed_stages()))}. Their numbers "
                "are absent above, not zero.</p>"
            )
        if cell.cross_check_performed is False:
            warnings.append(
                '<p class="banner note-banner">The pygambit/lrsnash cross-check '
                "was <b>skipped</b> (lrslib not installed): the Nash figures "
                "come from one solver, unverified against a second.</p>"
            )

        covers = (
            f" · covers {len(cell.grid_points)} grid points"
            if len(cell.grid_points) > 1 else ""
        )
        blocks.append(
            f"<h3>t = {cell.t:g}, α = {cell.alpha:g}{covers}</h3>"
            f"{''.join(warnings)}"
            f"{_artefact_links(cell, artefact_base)}"
        )

    return (
        "<h2>Artefacts</h2>"
        '<p class="note">Every number on this page traces to a file below. '
        "Each analysed matrix has its own directory, named "
        "<code>&lt;zoo&gt;_t&lt;NNN&gt;_a&lt;NNN&gt;_&lt;hash&gt;</code> — the "
        "hash is of the action-pair cells, so the same analysis always lands in "
        "the same place and sweeps are reproducible.</p>"
        + "".join(blocks)
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
# Deep-dive sections — one per analysis stage
#
# Two presentations, chosen by what the stage produces:
#   * a (t, α) GRID when the per-cell answer is small enough to read at a
#     glance (ESS names, face-class counts) — the whole plane at once;
#   * a (t, α) DROPDOWN when it is a figure or a table (invasion graph, Nash
#     components) — one cell at a time, everything pre-rendered and toggled.
# --------------------------------------------------------------------------


def _dial_selects(kind: str, ts: Sequence[float], alphas: Sequence[float]) -> str:
    """A `<select>` pair for picking a (t, α) cell within one section."""
    t_opts = "".join(f'<option value="{_key(t)}">t = {t:g}</option>' for t in ts)
    a_opts = "".join(f'<option value="{_key(a)}">α = {a:g}</option>' for a in alphas)
    return (
        f'<div class="picker">'
        f'<label for="{kind}-t">transparency t</label>'
        f'<select id="{kind}-t" class="dial" data-kind="{kind}">{t_opts}</select>'
        f'<label for="{kind}-a">caution α</label>'
        f'<select id="{kind}-a" class="dial" data-kind="{kind}">{a_opts}</select>'
        f"</div>"
    )


def _grid_table(
    ts: Sequence[float],
    alphas: Sequence[float],
    index: dict[tuple[str, str], Cell],
    render_cell,
    corner: str = "α \\ t",
) -> str:
    """The (t, α) plane as an HTML table — α down the rows, t across.

    A table rather than an SVG because these cells hold TEXT (bot names, four
    counts), which an SVG grid would clip. It also makes the whole plane
    copy-pasteable and screen-reader navigable.
    """
    head = "".join(f"<th>t = {t:g}</th>" for t in ts)
    rows = []
    for alpha in alphas:
        cells = []
        for t in ts:
            cell = index.get((_key(t), _key(alpha)))
            cells.append(
                f"<td>{render_cell(cell)}</td>" if cell is not None
                else '<td class="missing">not analysed</td>'
            )
        rows.append(f"<tr><th>α = {alpha:g}</th>{''.join(cells)}</tr>")
    return (
        f'<div class="panel"><table class="plane">'
        f"<thead><tr><th>{html.escape(corner)}</th>{head}</tr></thead>"
        f"<tbody>{''.join(rows)}</tbody></table></div>"
    )


def _ess_section(ts, alphas, index) -> str:
    """ii.a — which single types are unbeatable, across the plane."""

    def render(cell: Cell) -> str:
        bots = cell.ess_bots()
        if bots is None:
            return '<span class="missing">stage not run</span>'
        if not bots:
            # The common case on this zoo, and a real result — not an error.
            return '<span class="none-found">none</span>'
        return "<br>".join(
            f'<span class="botpill">{html.escape(b)}</span>' for b in bots
        )

    return (
        "<h2>2 · Pure ESS</h2>"
        '<p class="note"><b>What this asks.</b> Suppose the whole population is '
        "a single bot type, and a few mutants of some other type appear. If no "
        "mutant can ever gain a foothold, that type is an <i>evolutionarily "
        "stable strategy</i> — a monoculture nothing can crack. It is the "
        "strongest form of “this is where things end up”.</p>"
        '<p class="note">Each cell lists the types that are a pure ESS at that '
        "<code>(t, α)</code>. <b>none</b> is a genuine finding, not a gap: it "
        "means every type in the zoo is invadable by something, so no "
        "monoculture survives.</p>"
        + _grid_table(ts, alphas, index, render)
    )


def _faces_section_grid(ts, alphas, index, chart: str = "") -> str:
    """ii.c — the face-equilibrium class counts, across the plane."""

    def render(cell: Cell) -> str:
        by_class = cell.faces_by_class
        if not by_class:
            return '<span class="missing">stage not run</span>'
        parts = [
            ("stable", by_class.get("asymp_stable", 0), "cls-stable"),
            ("stable/inv", by_class.get("asymp_stable_invadable", 0), "cls-invadable"),
            ("singular", by_class.get("singular", 0), "cls-muted"),
            ("non-interior", by_class.get("non_interior", 0), "cls-muted"),
        ]
        rows = "".join(
            f'<tr><td class="{css}">{label}</td>'
            f'<td class="num {css}">{value}</td></tr>'
            for label, value, css in parts
        )
        trunc = (
            '<div class="trunc">truncated</div>'
            if not cell.enumeration_complete else ""
        )
        return f'<table class="mini">{rows}</table>{trunc}'

    return (
        "<h2>4 · Face equilibria — can a MIXTURE be stable?</h2>"
        '<p class="note"><b>What this asks.</b> A population need not be one '
        "type. Take any subset of bots — is there a proportion of them that "
        "holds steady, where all members earn the same average payoff so none "
        "grows at the others’ expense? Every subset is checked "
        "(<code>2^N − N − 1</code> of them).</p>"
        '<p class="note">Two independent stability questions per subset. '
        "<b>stable</b> (<code>asymp_stable</code>) means the mix returns after "
        "a nudge <i>and</i> no outsider can invade it. <b>stable/inv</b> "
        "(<code>asymp_stable_invadable</code>) means it holds together "
        "internally but an outsider <i>can</i> break in — a coalition that is "
        "stable only while nobody else shows up. <b>singular</b> and "
        "<b>non-interior</b> are subsets with no valid equilibrium at all; "
        "they are recorded rather than dropped, which is why they dominate the "
        "counts.</p>"
        '<h3>How the count moves with transparency</h3>'
        '<p class="note">Stable plus stable-invadable faces, one line per '
        "caution threshold. A falling count means blur is destroying the "
        "coexisting mixtures, pushing the population toward monocultures.</p>"
        f"{chart}"
        "<h3>The classes, cell by cell</h3>"
        + _grid_table(ts, alphas, index, render)
    )


def _invasion_section(ts, alphas, index, artefact_base: str, chart: str = "") -> str:
    """ii.b — the invasion graph for one selected cell."""
    views = []
    for t in ts:
        for alpha in alphas:
            cell = index.get((_key(t), _key(alpha)))
            if cell is None:
                body = '<p class="note missing">This grid point was not analysed.</p>'
            else:
                svg = cell.invasion_svg()
                stats = (
                    f'<ul class="stats">'
                    f"<li><b>{_fmt(cell.edges_strict)}</b><span>strict edges</span></li>"
                    f"<li><b>{_fmt(cell.n_sccs)}</b><span>SCCs</span></li>"
                    f"<li><b>{_fmt(cell.n_cycles)}</b><span>simple cycles</span></li>"
                    f"</ul>"
                )
                if svg is not None:
                    figure = f'<div class="panel figure">{_inline_svg(svg)}</div>'
                else:
                    figure = (
                        '<p class="note missing">No figure for this cell — the '
                        "sweep ran with <code>--no-render</code>, or the "
                        "invasion stage failed. The counts above still hold.</p>"
                    )
                links = []
                for rel, label in (
                    ("invasion/report.md", "report"),
                    ("invasion/edges_strict.csv", "edges (CSV)"),
                    ("invasion/graph.gexf", "graph (GEXF)"),
                    ("invasion/condensation.svg", "condensation"),
                ):
                    if (cell.run_dir / rel).exists():
                        links.append(
                            f'<a href="{artefact_base}/{cell.run}/{rel}">'
                            f"{html.escape(label)}</a>"
                        )
                body = stats + figure + (
                    f'<p class="note">{" · ".join(links)}</p>' if links else ""
                )
            views.append(
                f'<div class="dial-view" data-kind="invasion" data-t="{_key(t)}" '
                f'data-alpha="{_key(alpha)}" hidden>{body}</div>'
            )

    return (
        "<h2>3 · Invasion graph — who displaces whom</h2>"
        '<p class="note"><b>What this asks.</b> Draw an arrow <code>i → j</code> '
        "whenever a few <code>i</code> mutants can invade a resident population "
        "of <code>j</code>. The shape of that graph explains the ESS verdict "
        "above: a type nothing points at is a candidate to be unbeatable, while "
        "a <b>cycle</b> (A invades B invades C invades A) means there is no "
        "endpoint at all — the population churns forever.</p>"
        '<p class="note"><b>Strongly connected components</b> are clusters where '
        "every type can reach every other. <b>Few SCCs</b> means most of the "
        "zoo is caught in one mutually-invadable tangle: whatever the "
        "population is, something can displace it. <b>Many SCCs</b> means it "
        "has fragmented into groups with a clear pecking order between them, "
        "so the dynamics can settle.</p>"
        "<h3>How the structure moves with transparency</h3>"
        '<p class="note">SCC count as the signal degrades, one line per caution '
        "threshold. Rising SCCs as <code>α</code> increases is caution breaking "
        "the tangle apart.</p>"
        f"{chart}"
        "<h3>The graph, cell by cell</h3>"
        + _dial_selects("invasion", ts, alphas)
        + "".join(views)
    )


def _nash_section(ts, alphas, index, heat: str = "", heat_label: str = "") -> str:
    """ii.d — Nash components for one selected cell, plus the phase plane."""
    views = []
    for t in ts:
        for alpha in alphas:
            cell = index.get((_key(t), _key(alpha)))
            if cell is None:
                body = '<p class="note missing">This grid point was not analysed.</p>'
            else:
                comps = cell.nash_components()
                if comps is None:
                    body = (
                        '<p class="note missing">The Nash stage did not run for '
                        "this sweep.</p>"
                    )
                elif not comps:
                    body = '<p class="note missing">No equilibria recorded.</p>'
                else:
                    rows = "".join(
                        f"<tr><td>{c['id']}</td>"
                        f'<td class="num">{c["n_equilibria"]}</td>'
                        f'<td class="num">{html.escape(str(c["payoff"]))}</td>'
                        f'<td class="num">{html.escape(str(c["coop_rate"]))}</td>'
                        f"<td>{' '.join(f'<span class=\"botpill\">{html.escape(b)}</span>' for b in c['bots'])}</td>"
                        f"</tr>"
                        for c in comps
                    )
                    total = sum(c["n_equilibria"] for c in comps)
                    unverified = (
                        '<p class="banner note-banner">The pygambit/lrsnash '
                        "cross-check was skipped for this run — these figures "
                        "come from one solver.</p>"
                        if cell.cross_check_performed is False else ""
                    )
                    body = (
                        f'<p class="note">{total} extreme equilibria in '
                        f"{len(comps)} component(s). Payoff and cooperation "
                        f"rate are exact rationals.</p>"
                        f'<div class="panel"><table class="fam">'
                        f"<thead><tr><th>component</th><th class=\"num\">equilibria</th>"
                        f'<th class="num">payoff</th><th class="num">Pr[(C,C)]</th>'
                        f"<th>bots involved</th></tr></thead>"
                        f"<tbody>{rows}</tbody></table></div>{unverified}"
                    )
            views.append(
                f'<div class="dial-view" data-kind="nash" data-t="{_key(t)}" '
                f'data-alpha="{_key(alpha)}" hidden>{body}</div>'
            )

    # Cells where the stage ran but produced nothing, versus cells where it
    # was never asked to run. Only the former needs explaining.
    failed = [
        (t, a) for t in ts for a in alphas
        if (c := index.get((_key(t), _key(a)))) is not None
        and "nash" in c.stages and not c.stages["nash"].get("ok")
    ]
    failure_note = (
        '<p class="banner warn"><b>Not computed at '
        + html.escape(", ".join(f"(t={t:g}, α={a:g})" for t, a in failed))
        + ".</b> The Nash stage failed at these points; see the Artefacts "
        "section for the error. This is a stage failure, not an absence of "
        "equilibria — Nash 1951 guarantees at least one exists, so a blank "
        "here never means “none”.</p>"
        if failed else ""
    )

    heat_block = (
        "<h3>Equilibrium count across the plane</h3>"
        f'<p class="note">{html.escape(heat_label[0].upper() + heat_label[1:])} '
        "at every analysed <code>(t, α)</code>. One hue, light→dark for "
        "magnitude; every tile also carries its value, so the colour is "
        "redundant with the number rather than the only way to read it. Use it "
        "to spot <i>where</i> behaviour changes — a block of similar numbers is "
        "one regime, a sharp jump between neighbours is a phase boundary. A "
        "dash means that point was not analysed.</p>"
        f'<div class="panel">{heat}</div>'
        if heat else ""
    )

    return (
        "<h2>5 · Nash equilibria — what is rational at all</h2>"
        '<p class="note"><b>What this asks.</b> Stepping back from evolution: '
        "treated as a plain two-player game, where does neither side want to "
        "deviate? This is a <i>weaker</i> condition than ESS — every ESS is a "
        "Nash equilibrium but not conversely — so it catches resting points the "
        "evolutionary sections above reject, and unlike ESS it can never come "
        "back empty (Nash 1951 guarantees one exists).</p>"
        '<p class="note"><b>How to read the count.</b> A <i>high</i> number is '
        "not good news: it means the game is badly under-determined, with many "
        "mutually incompatible outcomes all self-consistent and nothing in the "
        "rules picking between them.</p>"
        '<p class="note">Equilibria are grouped into <b>components</b> — '
        "connected sets that behave as one solution. Watch the spread in "
        "<code>Pr[(C,C)]</code>: a component at 1 is total cooperation, one at "
        "0 is total defection. Both being genuine equilibria of the same game "
        "is Critch’s Open Problem 2 made concrete.</p>"
        '<p class="note"><b>Why this stage is the slow one.</b> It enumerates '
        "extreme equilibria by vertex enumeration over best-response polytopes "
        "in exact rational arithmetic — no floating point anywhere — which "
        "costs seconds to a minute per matrix while the other three stages "
        "take milliseconds. That is also why a sweep deduplicates identical "
        "matrices rather than re-analysing every grid point.</p>"
        f"{failure_note}"
        f"{heat_block}"
        "<h3>The components, cell by cell</h3>"
        + _dial_selects("nash", ts, alphas)
        + "".join(views)
    )


def _replicator_section(ts, alphas, index) -> str:
    """iii — where a population actually ENDS UP, and from how much of the space."""
    views = []
    for t in ts:
        for alpha in alphas:
            cell = index.get((_key(t), _key(alpha)))
            if cell is None:
                body = '<p class="note missing">This grid point was not analysed.</p>'
            else:
                data = cell.basins()
                if data is None:
                    body = ('<p class="note missing">The replicator stage did '
                            "not run for this sweep.</p>")
                else:
                    unconverged = (
                        f'<p class="banner warn"><b>{data["n_unconverged"]} of '
                        f'{data["n_interior_samples"] + data["n_vertex_samples"]} '
                        "trajectories did not settle.</b> They are excluded from "
                        "every basin below. A game with closed orbits cycles "
                        "forever instead of converging — that is a result about "
                        "the dynamics, not a numerical failure.</p>"
                        if data["n_unconverged"] else ""
                    )
                    rows = []
                    for a in data["attractors"]:
                        if not a["n_interior"] and not a["n_vertex"]:
                            continue
                        support = " ".join(
                            f'<span class="botpill">{html.escape(b)}</span>'
                            for b in a["support"]
                        ) or "—"
                        spread = a.get("spread", 0.0)
                        kind = (
                            "point" if spread < 1e-3
                            else f'<span title="endpoints spread over this '
                                 f'range — the rest points form a continuum">'
                                 f"continuum ±{spread:.2f}</span>"
                        )
                        reached = ", ".join(a["vertex_sources"]) or "—"
                        rows.append(
                            f'<tr><td class="num">{a["basin_fraction"]:.1%}</td>'
                            f'<td class="num">{a["n_interior"]}</td>'
                            f"<td>{kind}</td><td>{support}</td>"
                            f'<td class="cls-muted">{html.escape(reached)}</td></tr>'
                        )
                    body = (
                        f"{unconverged}"
                        f'<p class="note">{data["n_interior_converged"]} of '
                        f'{data["n_interior_samples"]} interior starts settled. '
                        "Basins are shares of those; monoculture starts are "
                        "listed separately in the last column because they are "
                        "a measure-zero set.</p>"
                        f'<div class="panel"><table class="fam"><thead><tr>'
                        f'<th class="num">basin</th><th class="num">starts</th>'
                        f"<th>shape</th><th>surviving types</th>"
                        f"<th>reached from</th></tr></thead>"
                        f"<tbody>{''.join(rows)}</tbody></table></div>"
                    )
            views.append(
                f'<div class="dial-view" data-kind="replicator" data-t="{_key(t)}" '
                f'data-alpha="{_key(alpha)}" hidden>{body}</div>'
            )

    return (
        "<h2>6 · Replicator dynamics — where a population LANDS</h2>"
        '<p class="note"><b>What this asks.</b> Every section above catalogues '
        "resting points; none says which one a population actually reaches. "
        "This one does. Start from a mix, let the types that earn more than "
        "average grow — <code>ẋᵢ = xᵢ((Ax)ᵢ − xᵀAx)</code> — and see where the "
        "flow ends. Sample many starting mixes and the share reaching each "
        "outcome is its <b>basin of attraction</b>.</p>"
        '<p class="note"><b>Why it matters.</b> This turns "this equilibrium '
        'exists" into "this equilibrium captures 93% of starting conditions". '
        "A monoculture can be a perfectly good rest point with a basin of "
        "<i>zero</i> — reachable only by starting there, which is exactly the "
        "gap between being an equilibrium and being where things end up.</p>"
        '<p class="note"><b>Reading the shape column.</b> <code>point</code> '
        "means every start landed on the same mix. <code>continuum</code> means "
        "the endpoints spread across a face of neutrally-stable rest points: "
        "the population settles on that <i>set of types</i>, but the exact "
        "proportions depend on where it began. Outcomes are grouped by which "
        "types survive, not by proximity, because a continuum is one answer "
        "rather than one answer per sample.</p>"
        + _dial_selects("replicator", ts, alphas)
        + "".join(views)
    )


def _moran_section(ts, alphas, index) -> str:
    """iv — finite populations, where drift can beat selection."""
    views = []
    for t in ts:
        for alpha in alphas:
            cell = index.get((_key(t), _key(alpha)))
            if cell is None:
                body = '<p class="note missing">This grid point was not analysed.</p>'
            else:
                points = cell.moran_points()
                if points is None:
                    body = ('<p class="note missing">The Moran stage did not '
                            "run for this sweep.</p>")
                elif not points:
                    body = '<p class="note missing">No points recorded.</p>'
                else:
                    rows = []
                    for p in points:
                        stable = " ".join(
                            f'<span class="botpill">{html.escape(b)}</span>'
                            for b in p["stochastically_stable"]
                        ) or '<span class="none-found">none above the cut</span>'
                        top = ", ".join(
                            f"{html.escape(n)} {share:.0%}"
                            for n, share in p["stationary"][:3]
                        )
                        warn = "" if p["converged"] else ' <span class="missing">(solve did not converge)</span>'
                        rows.append(
                            f'<tr><td class="num">{p["population"]}</td>'
                            f'<td class="num">{p["beta"]:g}</td>'
                            f"<td>{stable}</td>"
                            f'<td class="cls-muted">{top}{warn}</td></tr>'
                        )
                    body = (
                        f'<div class="panel"><table class="fam"><thead><tr>'
                        f'<th class="num">M</th><th class="num">β</th>'
                        f"<th>stochastically stable</th>"
                        f"<th>time spent (top 3)</th></tr></thead>"
                        f"<tbody>{''.join(rows)}</tbody></table></div>"
                    )
            views.append(
                f'<div class="dial-view" data-kind="moran" data-t="{_key(t)}" '
                f'data-alpha="{_key(alpha)}" hidden>{body}</div>'
            )

    return (
        "<h2>7 · Moran process — what a FINITE population does</h2>"
        '<p class="note"><b>What this asks.</b> Section 6 assumes an infinite '
        "population, where a type with any advantage always spreads. Real "
        "populations are finite, and there random drift can wipe out a type "
        "that selection favours. This is the difference between cooperation "
        "being <i>reachable</i> and cooperation being <i>likely</i>.</p>"
        '<p class="note"><b>What is computed.</b> The chance a single mutant '
        "takes over (fixation probability), and from that the fraction of TIME "
        "the population spends as each type once mutations are rare — the "
        "types carrying the most time are <b>stochastically stable</b>. This "
        "can disagree with every earlier section: a type that is no ESS and "
        "sits inside a cycle can still dominate the long run if it is hard to "
        "invade and easy to reach.</p>"
        '<p class="note"><b>The two dials.</b> <code>M</code> is population '
        "size — smaller means drift matters more. <code>β</code> is selection "
        "intensity: <code>β → 0</code> is pure drift (every type equally "
        "likely, the sanity floor), large <code>β</code> is selection "
        "dominating. Watching a type's share climb with β is the signal that "
        "selection, not chance, is putting it there.</p>"
        + _dial_selects("moran", ts, alphas)
        + "".join(views)
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
/* The (t, α) plane as a table — used by the ESS and faces deep dives. */
table.plane { border-collapse:collapse; font-size:.82rem; width:100%; }
table.plane th, table.plane td { border:1px solid var(--border); padding:6px 9px;
                                 text-align:left; vertical-align:top; }
table.plane thead th { color:var(--muted); font-weight:500; background:var(--bg); }
table.plane tbody th { color:var(--muted); font-weight:500; white-space:nowrap; }
table.mini { border-collapse:collapse; font-size:.75rem; width:100%; }
table.mini td { border:0; padding:1px 0; }
table.mini td.num { text-align:right; font-variant-numeric:tabular-nums; }
.cls-stable { color:#0072b2; font-weight:600; }
.cls-invadable { color:#d55e00; }
.cls-muted { color:var(--muted); }
.trunc { color:#d55e00; font-size:.7rem; font-style:italic; margin-top:2px; }
.none-found { color:var(--muted); font-style:italic; }
.botpill { display:inline-block; background:var(--panel); border:1px solid var(--border);
           border-radius:4px; padding:0 .3rem; font-size:.75rem; margin:1px 1px 0 0;
           white-space:nowrap; }
.picker select { background:var(--bg); color:var(--fg); border:1px solid var(--border);
                 border-radius:6px; padding:.3rem .45rem; font-size:.85rem; }
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
        scc_chart = stable_chart = trend_note
    else:
        scc_chart = chart_or_note(scc_series, "SCCs")
        stable_chart = chart_or_note(stable_series, "stable faces")

    # The deep-dive sections each own a (t, α) dropdown pair, keyed by
    # data-kind so the invasion and Nash pickers move independently.
    dial_script = (
        "<script>(function(){\n"
        '  var kinds = ["invasion", "nash", "replicator", "moran"];\n'
        "  kinds.forEach(function(kind){\n"
        '    var tSel = document.getElementById(kind + "-t");\n'
        '    var aSel = document.getElementById(kind + "-a");\n'
        "    if (!tSel || !aSel) return;\n"
        "    var views = document.querySelectorAll(\n"
        "      '.dial-view[data-kind=\"' + kind + '\"]');\n"
        "    function show(){\n"
        "      views.forEach(function(el){\n"
        "        el.hidden = el.dataset.t !== tSel.value\n"
        "                 || el.dataset.alpha !== aSel.value;\n"
        "      });\n"
        "    }\n"
        '    tSel.addEventListener("change", show);\n'
        '    aSel.addEventListener("change", show);\n'
        "    show();\n"
        "  });\n"
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

    # The four per-stage deep dives, appended after the existing layout.
    # Each deep dive owns its trend chart: the cross-cell view and the
    # per-cell view of one analysis belong together, not in separate sections.
    ess_section = _ess_section(ts, alphas, index)
    invasion_section = _invasion_section(
        ts, alphas, index, artefact_base, chart=scc_chart)
    faces_deep_section = _faces_section_grid(
        ts, alphas, index, chart=stable_chart)
    nash_section = _nash_section(
        ts, alphas, index, heat=heat, heat_label=heat_label)
    replicator_section = _replicator_section(ts, alphas, index)
    moran_section = _moran_section(ts, alphas, index)
    artefacts_section = _artefacts_section(cells, artefact_base)

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

<p class="note"><b>The two dials.</b> <code>t</code> is <b>transparency</b> — a
property of the environment. At <code>t = 1</code> each bot sees exactly which
opponent it faces (Critch's open-source setting); as <code>t</code> falls the
signal blurs, and at <code>t = 0</code> a bot cannot tell its opponents apart
at all (the classical opaque Prisoner's Dilemma). <code>α</code> is
<b>caution</b> — a property of the agent: a bot cooperates only if at least an
<code>α</code> fraction of the opponents it might be facing are ones it would
cooperate with. The two are never conflated: transparency is what the world
reveals, caution is what the agent demands.</p>

<p class="note"><b>What each grid point is.</b> A tau tournament is run at that
<code>(t, α)</code>, giving one action pair per ordered bot pair. Those become
a payoff matrix under the donation convention, and that matrix is pushed
through four population analyses. Points whose action-pair cells coincide give
identical answers, so they are analysed once — that is what <b>saved by
dedup</b> counts.</p>

<p class="note"><b>Reading the charts below.</b> On every trend chart the
x-axis runs full transparency on the <b>left</b> to opaque on the <b>right</b>,
so moving rightward means the signal is degrading.</p>

<h2>1 · What was analysed</h2>
<p class="note">Each section below opens one population analysis: first what it
asks, then how it moves across the plane, then the answer at a cell you choose.
<b>Sections 2-5 ask which resting points EXIST</b>, from the strongest claim (a
single unbeatable type) to the weakest (any rational resting point at all).
<b>Sections 6-7 ask which one a population actually REACHES</b> — the question
the first four cannot answer, because an equilibrium can be perfectly valid and
still unreachable from anywhere but itself.</p>
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
<p class="note">The whole sweep in one table — every number on this page is
reachable here without touching a control. <code>—</code> means the stage did
not run or failed; it never means zero.</p>

{ess_section}

{invasion_section}

{faces_deep_section}

{nash_section}

{replicator_section}

{moran_section}

<h2>Provenance</h2>
<p class="note">Payoffs use the donation convention
<code>(D,C)=b, (C,C)=b−c, (D,D)=0, (C,D)=−c</code> with <code>b&gt;c&gt;0</code>.
Every stage writes an <code>assumptions.json</code> next to its outputs
recording the conventions it used; nothing on this page is imputed.</p>

{artefacts_section}
</main>
{dial_script}
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

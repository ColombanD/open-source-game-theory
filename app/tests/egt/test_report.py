"""The EGT HTML report.

Renders against real sweeps (the cheap stages) and asserts the properties a
reader depends on: the picker covers every grid point, missing data reads as
missing rather than zero, and conditional results stay flagged.
"""

from __future__ import annotations

import re

import pytest

from pd_runner.egt.pipeline import sweep
from pd_runner.egt.report import build_report, load_sweep

CHEAP = ("ess", "invasion", "faces")


@pytest.fixture(scope="module")
def swept(tmp_path_factory):
    """A 3×2 grid with dedup, rendered once and shared by the tests."""
    root = tmp_path_factory.mktemp("egt_report")
    sweep(
        zoo="default", ts=[1.0, 0.6, 0.2], alphas=[0.3, 0.8],
        out_root=root, stages=CHEAP, render=False,
    )
    return root, build_report(root)


def _panels(page: str) -> list[tuple[str, str]]:
    """The section-5 picker panels only.

    Scoped to `class="swap-view"`: the deep-dive sections use the same
    `data-t`/`data-alpha` attributes on `dial-view` elements, so an unscoped
    match would count those too.
    """
    return re.findall(
        r'class="swap-view" data-t="([^"]+)" data-alpha="([^"]+)"', page)


# --------------------------------------------------------------------------
# Loading
# --------------------------------------------------------------------------


def test_load_sweep_reads_every_run(swept):
    root, _ = swept
    summary, cells = load_sweep(root)
    assert summary["zoo"] == "default"
    assert len(cells) == summary["n_distinct_matrices"]


def test_load_sweep_raises_without_runs(tmp_path):
    with pytest.raises(FileNotFoundError, match="run a sweep first"):
        load_sweep(tmp_path)


# --------------------------------------------------------------------------
# The (t, α) picker — the core of the page
# --------------------------------------------------------------------------


def test_picker_covers_every_grid_point(swept):
    """One panel per grid point, including points folded away by dedup."""
    _, page = swept
    panels = _panels(page)
    assert len(panels) == 6                      # 3 t × 2 α
    assert len(set(panels)) == 6                 # no duplicates
    assert {t for t, _ in panels} == {"1", "0.6", "0.2"}
    assert {a for _, a in panels} == {"0.3", "0.8"}


def test_deduped_points_get_their_own_panel(swept):
    """A folded point must still be selectable, showing the shared analysis."""
    root, page = swept
    _, cells = load_sweep(root)
    shared = [c for c in cells if len(c.grid_points) > 1]
    assert shared, "expected at least one deduped matrix in this grid"
    for cell in shared:
        for t, alpha in cell.grid_points:
            assert (f"{t:g}", f"{alpha:g}") in _panels(page)


def test_picker_slider_bounds_match_the_axes(swept):
    _, page = swept
    ts = re.search(r"var ts = (\[[^\]]*\])", page).group(1)
    assert ts.count(",") == 2                    # three transparencies
    t_max = re.search(r'id="t-slider"[^>]*max="(\d+)"', page).group(1)
    a_max = re.search(r'id="a-slider"[^>]*max="(\d+)"', page).group(1)
    assert (t_max, a_max) == ("2", "1")


# --------------------------------------------------------------------------
# Honesty: missing is missing, conditional is flagged
# --------------------------------------------------------------------------


def test_absent_stage_is_not_reported_as_zero(swept):
    """Nash did not run, so its cells must show the dash, never 0."""
    _, page = swept
    assert "nothing to plot" in page
    assert "<td class=\"num\">—</td>" in page


def test_conditional_results_are_flagged(swept):
    _, page = swept
    assert "stipulated (unproven) cells" in page
    assert "conditional" in page


def test_conditional_banner_is_not_repeated_per_panel(swept):
    """When every matrix is conditional, say it once, not once per panel."""
    _, page = swept
    assert page.count("<b>Conditional.</b>") == 0


def test_heatmap_falls_back_to_an_available_metric(swept):
    """Without the nash stage the phase plane still renders something."""
    _, page = swept
    assert "No data for this metric" not in page
    assert "darker = higher" in page


# --------------------------------------------------------------------------
# Page integrity
# --------------------------------------------------------------------------


def test_page_is_self_contained(swept):
    """No external assets — the page must work from file://."""
    _, page = swept
    assert "<script src=" not in page
    assert 'rel="stylesheet"' not in page
    assert "http://" not in page.replace("http://www.w3.org", "")


def test_every_template_placeholder_was_filled(swept):
    _, page = swept
    assert not re.search(r"\{[a-z_]+\}", page)


def test_table_view_lists_every_matrix(swept):
    """The table is the non-interactive path to every number on the page."""
    root, page = swept
    _, cells = load_sweep(root)
    table = page[page.find("Every matrix, side by side"):]
    for cell in cells:
        assert f"t={cell.t:g}, α={cell.alpha:g}" in table


def test_artefact_links_point_at_files_not_directories(swept):
    """StaticFiles has no directory listing, so bare dir links would 404."""
    _, page = swept
    for href in re.findall(r'href="(runs/[^"]+)"', page):
        assert not href.endswith("/"), f"directory link would 404: {href}"


def test_charts_are_inline_svg(swept):
    _, page = swept
    assert page.count("<svg") >= 3
    assert "<img" not in page


# --------------------------------------------------------------------------
# The per-stage deep dives (sections 7-10)
# --------------------------------------------------------------------------


def test_all_four_deep_dive_sections_are_present(swept):
    _, page = swept
    for heading in ("7 · Pure ESS", "8 · Invasion graph",
                    "9 · Face equilibria", "10 · Nash equilibria"):
        assert heading in page


def test_original_layout_is_preserved(swept):
    """Sections 1-6 must be untouched and still come first."""
    _, page = swept
    order = [page.find(f"<h2>{n} ·") for n in range(1, 11)]
    assert all(p > 0 for p in order), "a numbered section is missing"
    assert order == sorted(order), "sections are out of order"
    assert page.find("<h2>Provenance</h2>") > order[-1]


def test_each_deep_dive_explains_itself(swept):
    """All four sections lead with what the analysis is asking."""
    _, page = swept
    assert page.count("<b>What this asks.</b>") == 4


def test_ess_grid_covers_the_plane(swept):
    """One cell per (t, α), including deduped points."""
    root, page = swept
    section = page[page.find("<h2>7 ·"):page.find("<h2>8 ·")]
    plane = re.search(r'<table class="plane">.*?</table>', section, re.S).group(0)
    assert plane.count("<tr>") == 1 + 2          # header + 2 α rows
    assert plane.count("<td") == 6               # 3 t × 2 α


def test_ess_none_is_distinguished_from_stage_absent(swept):
    """"none" (a real finding) must not read like "stage not run"."""
    _, page = swept
    section = page[page.find("<h2>7 ·"):page.find("<h2>8 ·")]
    assert 'class="none-found">none<' in section
    assert "stage not run" not in section


def test_faces_grid_reports_all_four_classes(swept):
    root, page = swept
    section = page[page.find("<h2>9 ·"):page.find("<h2>10 ·")]
    minis = re.findall(r'<table class="mini">(.*?)</table>', section, re.S)
    assert len(minis) == 6                        # one per grid point
    for mini in minis:
        for label in ("stable", "stable/inv", "singular", "non-interior"):
            assert f">{label}</td>" in mini


def test_invasion_and_nash_have_independent_dial_pairs(swept):
    _, page = swept
    for kind in ("invasion", "nash"):
        assert f'id="{kind}-t"' in page
        assert f'id="{kind}-a"' in page


def test_dial_views_cover_every_grid_point_per_kind(swept):
    _, page = swept
    for kind in ("invasion", "nash"):
        views = re.findall(
            rf'data-kind="{kind}" data-t="([^"]+)" data-alpha="([^"]+)"', page)
        assert len(views) == 6, f"{kind} has {len(views)} views, expected 6"
        assert len(set(views)) == 6


def test_nash_section_says_the_stage_is_absent(swept):
    """This fixture skips nash; the section must say so, not show an empty table."""
    _, page = swept
    section = page[page.find("<h2>10 ·"):]
    assert "did not run" in section
    assert "<th>component</th>" not in section


# --------------------------------------------------------------------------
# The deep dives with a full four-stage sweep
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def swept_with_nash(tmp_path_factory):
    """A single cell through ALL FOUR stages — Nash costs ~50s, so just one."""
    root = tmp_path_factory.mktemp("egt_report_nash")
    sweep(zoo="default", ts=[1.0], alphas=[0.5], out_root=root, render=False)
    return root, build_report(root)


def test_nash_component_table_has_the_requested_columns(swept_with_nash):
    _, page = swept_with_nash
    section = page[page.find("<h2>10 ·"):]
    for column in ("component", "equilibria", "payoff", "Pr[(C,C)]", "bots involved"):
        assert f">{column}</th>" in section


def test_nash_components_report_the_cooperation_split(swept_with_nash):
    """The cooperative and defecting components must both be visible."""
    root, page = swept_with_nash
    _, cells = load_sweep(root)
    comps = cells[0].nash_components()
    assert comps is not None and len(comps) >= 2
    coop_rates = {c["coop_rate"] for c in comps}
    assert {"1/1", "0/1"} <= coop_rates, f"expected both extremes, got {coop_rates}"


def test_nash_components_name_the_bots_involved(swept_with_nash):
    root, _ = swept_with_nash
    _, cells = load_sweep(root)
    for comp in cells[0].nash_components():
        assert comp["bots"], "a component with no bots is meaningless"
        assert comp["n_equilibria"] >= 1


def test_ess_bots_none_versus_empty(swept_with_nash):
    """None = stage absent; [] = stage ran and found no ESS. Never conflate."""
    root, _ = swept_with_nash
    _, cells = load_sweep(root)
    assert cells[0].ess_bots() == []          # ran, found none
    assert cells[0].nash_components() is not None

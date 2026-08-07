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
    return re.findall(r'data-t="([^"]+)" data-alpha="([^"]+)"', page)


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

"""The EGT HTML report.

Renders against real sweeps (the cheap stages) and asserts the properties a
reader depends on: every grid point stays reachable, missing data reads as
missing rather than zero, and conditional results stay flagged.
"""

from __future__ import annotations

import re

import pytest

from pd_runner.egt.pipeline import sweep
from pd_runner.egt.report import build_report, load_sweep

CHEAP = ("ess", "invasion", "faces", "replicator", "moran")


@pytest.fixture(scope="module")
def swept(tmp_path_factory):
    """A 3×2 grid with dedup, rendered once and shared by the tests.

    `replicator_samples` is cut hard: these tests check that the SECTIONS
    render and stay honest, not that the basins are well estimated (that is
    `test_replicator.py`'s job, against games with known answers). At the
    production default of 200 this fixture alone took 14 minutes.
    """
    root = tmp_path_factory.mktemp("egt_report")
    sweep(
        zoo="body", ts=[1.0, 0.6, 0.2], alphas=[0.3, 0.8],
        out_root=root, stages=CHEAP, render=False,
        replicator_samples=8,
    )
    return root, build_report(root)


def _dial_views(page: str, kind: str) -> list[tuple[str, str]]:
    """The (t, α) views belonging to one deep-dive section."""
    return re.findall(
        rf'data-kind="{kind}" data-t="([^"]+)" data-alpha="([^"]+)"', page)


# --------------------------------------------------------------------------
# Loading
# --------------------------------------------------------------------------


def test_load_sweep_reads_every_run(swept):
    root, _ = swept
    summary, cells = load_sweep(root)
    assert summary["zoo"] == "body"
    assert len(cells) == summary["n_distinct_matrices"]


def test_load_sweep_raises_without_runs(tmp_path):
    with pytest.raises(FileNotFoundError, match="run a sweep first"):
        load_sweep(tmp_path)


# --------------------------------------------------------------------------
# Cell coverage — every grid point stays reachable
#
# The section-5 slider picker was removed; the invasion and Nash dropdowns are
# now the per-cell views, and they carry the same obligation: no grid point may
# become unreachable, including points folded away by dedup.
# --------------------------------------------------------------------------


def test_dropdowns_cover_every_grid_point(swept):
    for kind in ("invasion", "nash", "replicator", "moran"):
        views = _dial_views(swept[1], kind)
        assert len(views) == 6, f"{kind}: {len(views)} views, expected 3 t × 2 α"
        assert len(set(views)) == 6, f"{kind}: duplicate views"
        assert {t for t, _ in views} == {"1", "0.6", "0.2"}
        assert {a for _, a in views} == {"0.3", "0.8"}


def test_deduped_points_remain_selectable(swept):
    """A folded point must still be pickable, showing the shared analysis."""
    root, page = swept
    _, cells = load_sweep(root)
    shared = [c for c in cells if len(c.grid_points) > 1]
    assert shared, "expected at least one deduped matrix in this grid"
    for kind in ("invasion", "nash", "replicator", "moran"):
        views = set(_dial_views(page, kind))
        for cell in shared:
            for t, alpha in cell.grid_points:
                assert (f"{t:g}", f"{alpha:g}") in views


def test_dropdown_options_match_the_axes(swept):
    _, page = swept
    for kind in ("invasion", "nash", "replicator", "moran"):
        block = page[page.index(f'id="{kind}-t"'):]
        t_opts = re.findall(r'value="([^"]+)"', block[:block.index("</select>")])
        assert t_opts == ["1", "0.6", "0.2"]


def test_removed_slider_picker_leaves_nothing_behind(swept):
    """Section 5 is gone — no orphan markup or dead script."""
    _, page = swept
    for orphan in ("swap-view", "t-slider", "a-slider", "Pick a cell"):
        assert orphan not in page, f"leftover from the removed picker: {orphan}"


# --------------------------------------------------------------------------
# Honesty: missing is missing, conditional is flagged
# --------------------------------------------------------------------------


def test_absent_stage_is_not_reported_as_zero(swept):
    """Nash did not run in this fixture, so it must read as absent, not 0."""
    _, page = swept
    # The overview table dashes the missing columns…
    assert '<td class="num">—</td>' in page
    # …and the Nash section says the stage did not run rather than
    # rendering an empty component table.
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    assert "did not run" in section
    assert "<th>component</th>" not in section


def test_conditional_results_are_flagged(tmp_path):
    """A matrix resting on stipulated cells must carry the page-level banner.

    Every registered zoo has been fully proven since 2026-08-25, so a real
    sweep can no longer produce a conditional matrix; the banner is exercised
    on a hand-built run whose summary declares `is_fully_proven: false` — the
    flag `load_sweep` reads.
    """
    import json

    from pd_runner.egt.report import build_report

    run = tmp_path / "runs" / "body_t050_a050_c0ffee00"
    (run / "ess").mkdir(parents=True)
    (run / "ess" / "ess_summary.csv").write_text("type,is_ESS\nDefectBot,False\n")
    (run / "summary.json").write_text(json.dumps({
        "run": "body_t050_a050_c0ffee00", "zoo": "body",
        "t": 0.5, "alpha": 0.5, "fingerprint": "c0ffee00",
        "n_types": 1, "bots": ["DefectBot"], "excluded_bots": [],
        "is_fully_proven": False, "grid_points": [[0.5, 0.5]], "ok": True,
        "stages": {
            "ess": {"ok": True, "seconds": 0.0, "error": None, "n_pure_ess": 0},
        },
    }))

    page = build_report(tmp_path)
    assert "stipulated (unproven) cells" in page
    assert "conditional" in page


def test_fully_proven_sweep_carries_no_conditional_banner(swept):
    """The real zoos are kernel-clean, and the page must say so, not warn."""
    _, page = swept
    assert "stipulated (unproven) cells" not in page


def test_conditional_banner_is_stated_once(swept):
    """When every matrix is conditional, say it once at page level."""
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
    table = page[page.find("<h2>1 ·"):page.find("<h2>2 ·")]
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
# The per-stage deep dives (sections 2-5)
# --------------------------------------------------------------------------


def test_all_four_deep_dive_sections_are_present(swept):
    _, page = swept
    for heading in ("2 · Pure ESS", "3 · Invasion graph",
                    "4 · Face equilibria", "5 · Nash equilibria",
                    "6 · Replicator dynamics", "7 · Moran process"):
        assert heading in page


def test_original_layout_is_preserved(swept):
    """The overview table leads, then one section per analysis."""
    _, page = swept
    order = [page.find(f"<h2>{n} ·") for n in range(1, 8)]
    assert all(p > 0 for p in order), "a numbered section is missing"
    assert order == sorted(order), "sections are out of order"
    assert page.find("<h2>Provenance</h2>") > order[-1]


def test_each_deep_dive_explains_itself(swept):
    """All four sections lead with what the analysis is asking."""
    _, page = swept
    assert page.count("<b>What this asks.</b>") == 6


def test_ess_grid_covers_the_plane(swept):
    """One cell per (t, α), including deduped points."""
    root, page = swept
    section = page[page.find("<h2>2 ·"):page.find("<h2>3 ·")]
    plane = re.search(r'<table class="plane">.*?</table>', section, re.S).group(0)
    assert plane.count("<tr>") == 1 + 2          # header + 2 α rows
    assert plane.count("<td") == 6               # 3 t × 2 α


def test_ess_none_is_distinguished_from_stage_absent(swept):
    """"none" (a real finding) must not read like "stage not run"."""
    _, page = swept
    section = page[page.find("<h2>2 ·"):page.find("<h2>3 ·")]
    assert 'class="none-found">none<' in section
    assert "stage not run" not in section


def test_faces_grid_reports_all_four_classes(swept):
    root, page = swept
    section = page[page.find("<h2>4 ·"):page.find("<h2>5 ·")]
    minis = re.findall(r'<table class="mini">(.*?)</table>', section, re.S)
    assert len(minis) == 6                        # one per grid point
    for mini in minis:
        for label in ("stable", "stable/inv", "singular", "non-interior"):
            assert f">{label}</td>" in mini


def test_invasion_and_nash_have_independent_dial_pairs(swept):
    _, page = swept
    for kind in ("invasion", "nash", "replicator", "moran"):
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
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    assert "did not run" in section
    assert "<th>component</th>" not in section


# --------------------------------------------------------------------------
# The deep dives with a full four-stage sweep
# --------------------------------------------------------------------------


@pytest.fixture(scope="module")
def swept_with_nash(tmp_path_factory):
    """A single cell through ALL FOUR stages — Nash costs ~50s, so just one."""
    root = tmp_path_factory.mktemp("egt_report_nash")
    sweep(zoo="body", ts=[1.0], alphas=[0.5], out_root=root, render=False)
    return root, build_report(root)


def test_nash_component_table_has_the_requested_columns(swept_with_nash):
    _, page = swept_with_nash
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    for column in ("component", "equilibria", "payoff", "Pr[(C,C)]", "bots involved"):
        assert f">{column}</th>" in section


def test_nash_components_report_the_cooperation_split(swept_with_nash):
    """The cooperative and defecting components must both be visible."""
    root, page = swept_with_nash
    _, cells = load_sweep(root)
    comps = cells[0].nash_components()
    assert comps is not None and len(comps) >= 2
    # Displayed form: whole numbers drop the `/1` (see `_fmt_rational`).
    coop_rates = {c["coop_rate"] for c in comps}
    assert {"1", "0"} <= coop_rates, f"expected both extremes, got {coop_rates}"


def test_nash_components_name_the_bots_involved(swept_with_nash):
    root, _ = swept_with_nash
    _, cells = load_sweep(root)
    for comp in cells[0].nash_components():
        assert comp["bots"], "a component with no bots is meaningless"
        assert comp["n_equilibria"] >= 1


def test_whole_numbers_drop_the_denominator(swept_with_nash):
    """`2/1` displays as `2`; the noise is gone but the value is unchanged."""
    _, page = swept_with_nash
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    assert "/1<" not in section, "a `/1` denominator survived into the table"


def test_real_fractions_are_never_rounded(swept_with_nash):
    """A non-terminating value must stay exact — that is the point."""
    from pd_runner.egt.report import _fmt_range, _fmt_rational

    assert _fmt_rational("6/7") == "6/7"          # 0.857142857… never rounded
    assert _fmt_rational("43/147") == "43/147"
    assert _fmt_rational("3/2") == "3/2"
    assert _fmt_rational("2/1") == "2"
    assert _fmt_rational("-1/1") == "-1"
    # Ranges format both ends.
    assert _fmt_range(["0/1", "2/1"]) == "0…2"
    assert _fmt_range(["6/7", "3/2"]) == "6/7…3/2"
    assert _fmt_range([]) == "—"


def test_display_formatting_does_not_touch_the_artefacts(swept_with_nash):
    """The on-disk schema is pinned and machine-read: it keeps `n/d`."""
    import json

    root, _ = swept_with_nash
    files = sorted(root.glob("runs/*/nash/runs/*/equilibria.jsonl"))
    assert files, "expected a nash artefact"
    record = json.loads(files[0].read_text().splitlines()[0])
    assert "/" in record["u_rational"]
    assert "/" in record["cooperation_rate_rational"]


def test_nash_explains_its_cost(swept_with_nash):
    """The section says why it is the slow stage, since that shapes sweeps."""
    _, page = swept_with_nash
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    assert "exact rational arithmetic" in section
    assert "deduplicates" in section


def test_nash_failure_is_named_and_never_reads_as_no_equilibria(tmp_path):
    """A failed Nash stage must be called out as a failure, not a blank.

    Nash 1951 guarantees an equilibrium exists, so an empty cell can only ever
    mean the computation did not happen — the page has to say which.
    """
    import json

    from pd_runner.egt.report import build_report

    # Hand-build a run whose nash stage failed, which is what the reader sees
    # when e.g. the solver crashes on a degenerate matrix.
    run = tmp_path / "runs" / "body_t000_a030_deadbeef"
    (run / "ess").mkdir(parents=True)
    (run / "ess" / "ess_summary.csv").write_text("type,is_ESS\nDefectBot,False\n")
    (run / "summary.json").write_text(json.dumps({
        "run": "body_t000_a030_deadbeef", "zoo": "body",
        "t": 0.0, "alpha": 0.3, "fingerprint": "deadbeef",
        "n_types": 1, "bots": ["DefectBot"], "excluded_bots": [],
        "is_fully_proven": True, "grid_points": [[0.0, 0.3]], "ok": False,
        "stages": {
            "ess": {"ok": True, "seconds": 0.0, "error": None, "n_pure_ess": 0},
            "nash": {"ok": False, "seconds": 0.0,
                     "error": "IndexError: list index out of range"},
        },
    }))

    page = build_report(tmp_path)
    section = page[page.find("<h2>5 ·"):page.find("<h2>6 ·")]
    assert "Not computed at" in section
    assert "(t=0, α=0.3)" in section
    assert "not an absence of equilibria" in section
    # The error itself stays reachable in the artefacts section.
    assert "IndexError" in page or "Failed stages" in page


def test_ess_bots_none_versus_empty(swept_with_nash):
    """None = stage absent; [] = stage ran and found no ESS. Never conflate."""
    root, _ = swept_with_nash
    _, cells = load_sweep(root)
    assert cells[0].ess_bots() == []          # ran, found none
    assert cells[0].nash_components() is not None


# --------------------------------------------------------------------------
# Sections 6-7: which equilibrium is actually REACHED
# --------------------------------------------------------------------------


def test_dynamics_sections_explain_the_gap_they_close(swept):
    """The point of 6-7 is reachability, not another list of equilibria."""
    _, page = swept
    overview = page[page.find("<h2>1 ·"):page.find("<h2>2 ·")]
    assert "actually REACHES" in overview

    replicator = page[page.find("<h2>6 ·"):page.find("<h2>7 ·")]
    assert "basin of attraction" in replicator
    assert "captures 93% of starting conditions" in replicator

    moran = page[page.find("<h2>7 ·"):page.find("<h2>Provenance")]
    assert "reachable" in moran and "likely" in moran


def test_replicator_section_reports_basins_and_shape(swept):
    _, page = swept
    section = page[page.find("<h2>6 ·"):page.find("<h2>7 ·")]
    for column in ("basin", "starts", "shape", "surviving types", "reached from"):
        assert f">{column}</th>" in section
    # A continuum must be labelled as one, not passed off as a point.
    assert "continuum" in section or "point" in section


def test_moran_section_reports_the_two_dials(swept):
    _, page = swept
    section = page[page.find("<h2>7 ·"):page.find("<h2>Provenance")]
    assert ">M</th>" in section and ">β</th>" in section
    assert "stochastically stable" in section


def test_basins_and_moran_are_read_from_the_artefacts(swept):
    """`None` = stage absent, never conflated with an empty result."""
    root, _ = swept
    _, cells = load_sweep(root)
    for cell in cells:
        basins = cell.basins()
        assert basins is not None, "the replicator stage ran in this fixture"
        assert basins["n_interior_converged"] <= basins["n_interior_samples"]
        points = cell.moran_points()
        assert points, "the moran stage ran in this fixture"
        assert all("stochastically_stable" in p for p in points)

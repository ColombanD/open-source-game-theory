"""Run directories and the (t, α) sweep driver.

The Nash stage costs ~50s on an 11-type game, so these tests drive the cheap
stages (`ess`, `invasion`, `faces`) and cover Nash separately in
`test_nash_pipeline.py`.
"""

from __future__ import annotations

import json

import pytest

from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
from pd_runner.egt.pipeline import (
    DEFAULT_ALPHAS,
    RunPaths,
    _fmt_dial,
    alpha_phase_representatives,
    analyse_matrix,
    cells_fingerprint,
    linear_ts,
    run_stages,
    sweep,
)

CHEAP = ("ess", "invasion", "faces")


@pytest.fixture(scope="module")
def tau_matrix():
    from pd_runner.tau.matrix import get_zoo

    return get_zoo("body").load()


@pytest.fixture(scope="module")
def base_payoff(tau_matrix):
    return payoff_matrix_from_tau_matrix(tau_matrix, zoo="body")


# --------------------------------------------------------------------------
# Run directory naming
# --------------------------------------------------------------------------


@pytest.mark.parametrize(
    "value,expected",
    [(1.0, "100"), (0.0, "000"), (0.62, "062"), (0.3, "030"), (None, "na")],
)
def test_fmt_dial(value, expected):
    assert _fmt_dial(value) == expected


def test_t_extremes_do_not_collide():
    """t=1.0 and t=0.0 must produce different directory names."""
    assert _fmt_dial(1.0) != _fmt_dial(0.0)


def test_run_dir_encodes_zoo_dials_and_fingerprint(base_payoff, tmp_path):
    paths = RunPaths.for_matrix(base_payoff, tmp_path)
    assert paths.name.startswith("body_t100_ana_")
    assert paths.numeric_csv == paths.run_dir / "ess" / "payoff_matrix_numeric.csv"
    assert paths.stage_dir("nash").parent == paths.run_dir


def test_fingerprint_tracks_cells_not_identity(tau_matrix, base_payoff):
    """Equal cells => equal fingerprint; different cells => different."""
    from pd_runner.tau.sweep import run_tournament
    from pd_runner.egt.ingest import payoff_matrix_from_tournament

    # t=1 reproduces the base matrix (anchor theorem).
    anchored = payoff_matrix_from_tournament(
        run_tournament(tau_matrix, t=1.0, alpha=0.5), bots=tau_matrix.bots, zoo="body"
    )
    assert cells_fingerprint(anchored) == cells_fingerprint(base_payoff)

    opaque = payoff_matrix_from_tournament(
        run_tournament(tau_matrix, t=0.0, alpha=0.8), bots=tau_matrix.bots, zoo="body"
    )
    assert cells_fingerprint(opaque) != cells_fingerprint(base_payoff)


# --------------------------------------------------------------------------
# Stage execution
# --------------------------------------------------------------------------


def test_run_stages_writes_artefacts_and_chains(base_payoff, tmp_path):
    paths = RunPaths.for_matrix(base_payoff, tmp_path)
    outcomes = run_stages(base_payoff, paths, stages=CHEAP, render=False)

    assert [o.stage for o in outcomes] == list(CHEAP)
    assert all(o.ok for o in outcomes), [o.error for o in outcomes if not o.ok]

    # ii.a writes the CSV that ii.b-ii.d consume — the inter-stage contract.
    assert paths.numeric_csv.exists()
    assert (paths.stage_dir("invasion") / "report.md").exists()
    assert (paths.stage_dir("faces") / "face_equilibria.parquet").exists()


def test_downstream_stages_fail_loudly_without_ess(base_payoff, tmp_path):
    """A missing numeric matrix is recorded as failure, never skipped silently."""
    paths = RunPaths.for_matrix(base_payoff, tmp_path)
    outcomes = run_stages(base_payoff, paths, stages=("invasion", "faces"), render=False)

    assert [o.ok for o in outcomes] == [False, False]
    assert all("ess" in (o.error or "") for o in outcomes)


def test_analyse_matrix_writes_summary(base_payoff, tmp_path):
    result = analyse_matrix(
        base_payoff, tmp_path, grid_points=[(1.0, 0.5)], stages=CHEAP, render=False
    )
    assert result.ok

    payload = json.loads((result.paths.run_dir / "summary.json").read_text())
    assert payload["zoo"] == "body"
    assert payload["grid_points"] == [[1.0, 0.5]]
    assert payload["n_types"] == len(base_payoff.bots)
    assert set(payload["stages"]) == set(CHEAP)
    assert payload["stages"]["ess"]["ok"] is True


def test_unknown_stage_is_recorded_as_failure(base_payoff, tmp_path):
    paths = RunPaths.for_matrix(base_payoff, tmp_path)
    outcomes = run_stages(base_payoff, paths, stages=("nonesuch",), render=False)
    assert outcomes[0].ok is False
    assert "unknown stage" in outcomes[0].error


# --------------------------------------------------------------------------
# The sweep + dedup
# --------------------------------------------------------------------------


def test_sweep_dedups_identical_matrices(tmp_path):
    """At t=1 the matrix is α-independent, so both α points share one run."""
    result = sweep(
        zoo="body", ts=[1.0], alphas=[0.3, 0.8],
        out_root=tmp_path, stages=CHEAP, render=False,
    )
    assert result.n_grid_points == 2
    assert result.n_distinct == 1
    assert result.runs[0].grid_points == [(1.0, 0.3), (1.0, 0.8)]


def test_dedup_is_recorded_in_the_run_summary(tmp_path):
    """The reused run's summary.json lists every grid point it covers."""
    result = sweep(
        zoo="body", ts=[1.0], alphas=[0.3, 0.8],
        out_root=tmp_path, stages=("ess",), render=False,
    )
    payload = json.loads((result.runs[0].paths.run_dir / "summary.json").read_text())
    assert payload["n_grid_points"] == 2
    assert payload["grid_points"] == [[1.0, 0.3], [1.0, 0.8]]


def test_sweep_separates_distinct_matrices(tmp_path):
    result = sweep(
        zoo="body", ts=[1.0, 0.0], alphas=[0.3, 0.8],
        out_root=tmp_path, stages=("ess",), render=False,
    )
    assert result.n_grid_points == 4
    # t=1 collapses to one matrix; the two t=0 points differ by α.
    assert result.n_distinct == 3
    assert len({r.paths.fingerprint for r in result.runs}) == 3


def test_sweep_writes_top_level_summary(tmp_path):
    result = sweep(
        zoo="body", ts=[1.0], alphas=[0.5],
        out_root=tmp_path, stages=("ess",), render=False,
    )
    payload = json.loads((tmp_path / "sweep_summary.json").read_text())
    assert payload["zoo"] == "body"
    assert payload["n_distinct_matrices"] == result.n_distinct
    assert payload["dedup_saved"] == result.n_grid_points - result.n_distinct
    assert payload["ok"] is True


def test_sweep_accepts_both_zoos(tmp_path):
    for zoo in ("body", "body+twins"):
        result = sweep(
            zoo=zoo, ts=[1.0], alphas=[0.5],
            out_root=tmp_path / zoo, stages=("ess",), render=False,
        )
        assert all(r.ok for r in result.runs)
        assert result.runs[0].paths.zoo == zoo


def test_tau_lift_terminates_even_over_a_nonterminating_bot():
    """A swept matrix has no "N" cells, so MirrorBot is NOT excluded.

    This is a real asymmetry between the two ingest paths, not an oversight:

      - `payoff_matrix_from_tau_matrix` reads BASE cells, where MirrorBot
        self-play is a proven `none` ("N"), so the exclusion policy drops it.
      - `payoff_matrix_from_tournament` reads TAU cells. `tau_play` thresholds
        a cooperation mass and `cooperates()` tests `== "C"`, so an "N" base
        cell counts as not-cooperating and the lift emits a real D. A TauBot
        always terminates, even when the bot it lifts does not.

    Consequence: a MirrorBot-holding matrix analyses one type fewer via the
    base path than anywhere in a sweep. Compare the two only with that in
    mind. (No registered zoo carries MirrorBot since 2026-09-01, so this runs
    on an explicit roster through the same tournament ingest the sweep uses.)
    """
    from pd_runner.egt.ingest import payoff_matrix_from_tournament
    from pd_runner.tau.matrix import load_tau_matrix
    from pd_runner.tau.sweep import run_tournament

    m = load_tau_matrix(
        bots=("MirrorBot", "DupocBot", "CooperateBot", "DefectBot"),
        hypothetical_cells={},
    )
    base = payoff_matrix_from_tau_matrix(m, zoo="mirror-roster")
    assert "MirrorBot" in base.excluded_bots

    payoff = payoff_matrix_from_tournament(
        run_tournament(m, t=1.0, alpha=0.5), bots=m.bots, zoo="mirror-roster"
    )
    assert payoff.excluded_bots == ()
    assert "MirrorBot" in payoff.bots
    assert not any("N" in pair for pair in payoff.cells.values())


# --------------------------------------------------------------------------
# Grid helpers
# --------------------------------------------------------------------------


def test_linear_ts_spans_the_dial_inclusive():
    ts = linear_ts(6)
    assert ts[0] == 1.0 and ts[-1] == 0.0
    assert len(ts) == 6
    assert ts == sorted(ts, reverse=True)


def test_linear_ts_never_degenerates():
    assert len(linear_ts(1)) == 2
    assert len(linear_ts(0)) == 2


def test_default_alphas_span_the_extremes():
    assert min(DEFAULT_ALPHAS) == 0.0
    assert max(DEFAULT_ALPHAS) == 1.0


def test_alpha_phase_representatives_are_sorted_and_bounded(tau_matrix):
    reps = alpha_phase_representatives(tau_matrix, t=0.5)
    assert reps == sorted(reps)
    assert all(0.0 <= a <= 1.0 for a in reps)
    assert reps[0] == 0.0 and reps[-1] == 1.0


def test_alpha_phases_collapse_at_full_transparency(tau_matrix):
    """At t=1 the mass is a point mass, so there are only the trivial phases.

    This is what makes α irrelevant at full transparency — the property the
    dedup exploits.
    """
    assert alpha_phase_representatives(tau_matrix, t=1.0) == [0.0, 0.5, 1.0]


def test_sweep_rejects_a_bad_alpha_keyword(tmp_path):
    with pytest.raises(ValueError, match="'phases'"):
        sweep(zoo="body", ts=[1.0], alphas="every", out_root=tmp_path, stages=("ess",))


def test_default_out_root_is_anchored_to_the_package_not_cwd(tmp_path, monkeypatch):
    """A relative default silently changes meaning with the working directory.

    Regression: `DEFAULT_OUT_ROOT` was `Path("generated/egt")`, so a sweep run
    from the repo root wrote ~120 artefact files to `./generated/`, outside the
    gitignore, and they turned up in `git status`.
    """
    from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

    monkeypatch.chdir(tmp_path)
    assert DEFAULT_OUT_ROOT.is_absolute()
    assert DEFAULT_OUT_ROOT.parts[-3:] == ("app", "generated", "egt")


def test_api_serves_runs_from_the_same_anchored_root():
    """The static mount and the sweep output must agree on one directory."""
    from pd_runner.api.main import _EGT_RUNS_DIR
    from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

    assert _EGT_RUNS_DIR == DEFAULT_OUT_ROOT / "runs"


def test_family_sweep_is_isolated_and_named(tmp_path):
    """The σ-family extension (2026-09-01): a non-behavioral sweep carries its
    family in every run-directory name and writes `sweep_summary_<family>.json`,
    so two families in one out_root never clobber each other; the behavioral
    path keeps the legacy naming byte-for-byte."""
    eps = sweep(zoo="body", ts=[1.0], alphas=[0.5], family="epsilon",
                out_root=tmp_path, stages=("ess",), render=False)
    assert eps.family == "epsilon"
    assert eps.summary_path.name == "sweep_summary_epsilon.json"
    assert eps.summary_path.exists()
    assert all("_epsilon_" in r.paths.name for r in eps.runs)
    assert all(r.summary()["family"] == "epsilon" for r in eps.runs)

    beh = sweep(zoo="body", ts=[1.0], alphas=[0.5], family="behavioral",
                out_root=tmp_path, stages=("ess",), render=False)
    assert beh.summary_path.name == "sweep_summary.json"
    assert beh.summary_path.exists()          # both summaries coexist
    assert eps.summary_path.exists()
    name = beh.runs[0].paths.name
    assert "behavioral" not in name and name.startswith("body_t100_a050_")

    # at t = 1 every family is the point-mass channel: same cells, same fingerprint
    assert eps.runs[0].paths.fingerprint == beh.runs[0].paths.fingerprint


def test_family_sweep_rejects_unknown_family(tmp_path):
    with pytest.raises(ValueError, match="unknown σ family"):
        sweep(zoo="body", ts=[1.0], alphas=[0.5], family="telepathic",
              out_root=tmp_path, stages=("ess",), render=False)

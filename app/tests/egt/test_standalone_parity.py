"""Parity with the standalone `egt-osgt` repo.

The `superficial-standalone` zoo feeds this pipeline byte-identical input to
what that repo analysed — including the six cells its hand-transcribed CSV got
wrong. Given the same input, the analyses must produce the same output; any
difference would be OURS.

The expected values are that repo's own published artefacts at commit
`bb51559` (`results/ess/`, `results/invasion/report.md`, `results/faces/
summary.md`, `results/nash/latest/`). This is the end-to-end check that the
port preserved the mathematics.
"""

from __future__ import annotations

import json

import pytest

from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
from pd_runner.egt.pipeline import RunPaths, run_stages
from pd_runner.tau.matrix import get_zoo

# Published by the standalone repo on exactly this matrix.
STANDALONE = {
    "n_pure_ess": 0,
    "edges_strict": 18,
    "n_sccs": 3,
    "n_cycles": 11,
    "n_supports": 247,
    "asymp_stable": 0,
    "asymp_stable_invadable": 3,
    "saddle": 3,
    "singular": 66,
    "non_interior": 175,
    "n_extreme_NE": 16,
    "n_components": 5,
}


@pytest.fixture(scope="module")
def analysed(tmp_path_factory):
    payoff = payoff_matrix_from_tau_matrix(
        get_zoo("superficial-standalone").load(), zoo="superficial-standalone"
    )
    paths = RunPaths.for_matrix(payoff, tmp_path_factory.mktemp("parity"))
    outcomes = run_stages(
        payoff, paths,
        stages=("ess", "invasion", "faces", "nash"),
        render=False,
    )
    assert all(o.ok for o in outcomes), [o.error for o in outcomes if not o.ok]
    return {o.stage: o.summary for o in outcomes}


def test_ess_matches(analysed):
    assert analysed["ess"]["n_pure_ess"] == STANDALONE["n_pure_ess"]


def test_invasion_graph_matches(analysed):
    got = analysed["invasion"]
    assert got["edges_strict"] == STANDALONE["edges_strict"]
    assert got["n_sccs"] == STANDALONE["n_sccs"]
    assert got["n_cycles"] == STANDALONE["n_cycles"]


def test_face_classification_matches(analysed):
    got = analysed["faces"]
    assert got["n_supports"] == STANDALONE["n_supports"]
    by_class = got["by_class"]
    for cls in ("asymp_stable", "asymp_stable_invadable", "saddle",
                "singular", "non_interior"):
        assert by_class.get(cls, 0) == STANDALONE[cls], f"{cls} differs"


def test_nash_enumeration_matches(analysed):
    got = analysed["nash"]
    assert got["n_extreme_NE"] == STANDALONE["n_extreme_NE"]
    assert got["n_components"] == STANDALONE["n_components"]


def test_parity_is_over_the_replay_zoo_not_the_certified_one():
    """Guard the premise: parity holds on the WRONG matrix, by construction.

    The certified 8-bot zoo gives different numbers because six cells differ.
    If this ever started matching too, the replay zoo would have stopped
    replaying anything.
    """
    from pd_runner.egt.static_analysis.cli import run_ess
    import tempfile
    from pathlib import Path

    certified = payoff_matrix_from_tau_matrix(
        get_zoo("critch8").load(), zoo="critch8"
    )
    replay = payoff_matrix_from_tau_matrix(
        get_zoo("superficial-standalone").load(), zoo="superficial-standalone"
    )
    assert not (certified.A == replay.A).all(), (
        "the two 8-bot zoos produce identical payoff matrices — the replay "
        "overrides are no longer taking effect"
    )

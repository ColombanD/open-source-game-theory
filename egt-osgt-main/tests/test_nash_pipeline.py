"""Real-data regression test for the Nash stage on the OSGT 8x8 game.

Runs the full pipeline (CLI as a function call) and checks invariants:
  - Both libraries agree.
  - Pure NE found directly are a subset of Method 2 output.
  - A symmetric NE exists (Nash 1951).
  - Cooperation-rate sanity on pure NE.
  - (DefectBot, DefectBot) is an NE and has coop rate 0.
  - (CooperateBot, CooperateBot) is NOT a pure NE (Cooperate is invaded).
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from src.nash.cli import run_pipeline


@pytest.fixture(scope="module")
def fresh_run(tmp_path_factory) -> Path:
    """Run the Nash pipeline once into a tmp dir; return that run's directory."""
    repo = Path(__file__).resolve().parent.parent
    out_dir = tmp_path_factory.mktemp("nash_out")
    run_dir = run_pipeline(
        raw_csv=repo / "data" / "payoff_matrix.csv",
        config_path=repo / "config.json",
        numeric_csv=repo / "results" / "ess" / "payoff_matrix_numeric.csv",
        inherited_assumptions_path=repo / "results" / "ess" / "assumptions.json",
        out_dir=out_dir,
        lrsnash_bin="lrsnash",
        lrsnash_timeout_seconds=300,
    )
    return run_dir


def _equilibria(run_dir: Path):
    with open(run_dir / "equilibria.jsonl") as f:
        return [json.loads(line) for line in f]


def test_libraries_agree(fresh_run):
    with open(fresh_run / "provenance.json") as f:
        prov = json.load(f)
    assert prov["cross_check_libraries_agree"] is True


def test_pure_NE_subset_of_method2(fresh_run):
    with open(fresh_run / "provenance.json") as f:
        prov = json.load(f)
    assert prov["n_pure_NE_direct"] <= prov["n_pure_NE_in_method2_output"]


def test_symmetric_NE_exists(fresh_run):
    eqs = _equilibria(fresh_run)
    assert any(e["classification"] == "symmetric" for e in eqs), (
        "Nash 1951: every finite symmetric game has a symmetric NE"
    )


def test_defect_bot_pure_NE_with_coop_rate_zero(fresh_run):
    eqs = _equilibria(fresh_run)
    # Find a pure NE where row and col both play DefectBot only.
    pure_defect = [
        e for e in eqs
        if e["support_row_names"] == ["DefectBot"]
        and e["support_col_names"] == ["DefectBot"]
    ]
    assert len(pure_defect) == 1
    assert pure_defect[0]["cooperation_rate_rational"] == "0/1"
    assert pure_defect[0]["u_rational"] == "0/1"


def test_cooperate_bot_is_not_pure_NE(fresh_run):
    eqs = _equilibria(fresh_run)
    pure_cc = [
        e for e in eqs
        if e["support_row_names"] == ["CooperateBot"]
        and e["support_col_names"] == ["CooperateBot"]
    ]
    assert pure_cc == [], (
        "CooperateBot is invaded by DefectBot, so (CooperateBot, CooperateBot) "
        "must not appear as a pure NE"
    )


def test_components_partition_extreme_NE(fresh_run):
    eqs = _equilibria(fresh_run)
    with open(fresh_run / "nash_components.json") as f:
        comps = json.load(f)
    member_lists = [c["extreme_NE_indices"] for c in comps["components"]]
    members = [i for lst in member_lists for i in lst]
    assert sorted(members) == sorted(e["index"] for e in eqs)
    # Disjoint.
    assert len(members) == len(set(members))


def test_every_NE_verified_on_original_A(fresh_run):
    eqs = _equilibria(fresh_run)
    assert all(e["verified_on_original_A"] for e in eqs)

"""Real-data regression test for the Nash stage over a certified zoo.

Runs the full pipeline (CLI as a function call) and checks invariants that
follow from the theory rather than from any particular matrix:
  - Pure NE found directly are a subset of Method 2 output.
  - A symmetric NE exists (Nash 1951).
  - Cooperation-rate sanity on pure NE.
  - (DefectBot, DefectBot) is an NE and has coop rate 0.
  - (CooperateBot, CooperateBot) is NOT a pure NE (Cooperate is invaded).
  - Components partition the extreme NE; every NE verifies on the original A.

Rebased from the standalone repo's hand-transcribed 8x8 CSV. The
"both libraries agree" assertion is now conditional: lrsnash is an optional
system binary (see `method2_lrsnash`), so the test asserts agreement only
when the cross-check actually ran.

This is the slowest test in the suite (~1 min: exact-rational vertex
enumeration over an 11-type game), hence the module-scoped fixture.
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from pd_runner.egt.nash.cli import run_pipeline

ZOO = "body"


@pytest.fixture(scope="module")
def fresh_run(tmp_path_factory) -> Path:
    """Run the ESS + Nash stages once into a tmp dir; return the run dir."""
    from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
    from pd_runner.egt.static_analysis.cli import run_ess
    from pd_runner.tau.matrix import get_zoo

    tmp = tmp_path_factory.mktemp("nash_out")
    payoff = payoff_matrix_from_tau_matrix(get_zoo(ZOO).load(), zoo=ZOO)

    # The Nash stage reads the numeric CSV the ESS stage writes, and
    # cross-checks it against the in-memory matrix.
    ess_dir = tmp / "ess"
    run_ess(payoff, ess_dir)

    return run_pipeline(
        payoff=payoff,
        numeric_csv=ess_dir / "payoff_matrix_numeric.csv",
        inherited_assumptions_path=ess_dir / "assumptions.json",
        out_dir=tmp / "nash",
    )


def _equilibria(run_dir: Path):
    with open(run_dir / "equilibria.jsonl") as f:
        return [json.loads(line) for line in f]


def test_libraries_agree(fresh_run):
    """When the cross-check ran, the two solvers must agree.

    `run_pipeline` raises on disagreement, so reaching here already implies
    agreement; this asserts the provenance RECORDS it faithfully — including
    recording `performed: false` when lrsnash is absent, which must never be
    written as a passed check.
    """
    with open(fresh_run / "provenance.json") as f:
        prov = json.load(f)

    if prov["cross_check_performed"]:
        assert prov["cross_check_libraries_agree"] is True
        assert "lrsnash" in prov["methods_used"]
    else:
        assert prov["cross_check_libraries_agree"] is False
        assert "lrsnash" not in prov["methods_used"]


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

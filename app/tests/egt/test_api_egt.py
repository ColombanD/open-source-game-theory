"""The `/egt/*` API surface.

`TestClient` runs FastAPI background tasks synchronously, so a POST returns
only after the sweep finishes — which is why every case here uses the cheap
stages and a one-point grid.
"""

from __future__ import annotations

import pytest
from fastapi.testclient import TestClient

from pd_runner.api.main import app


@pytest.fixture(scope="module", autouse=True)
def _tmp_out_root(tmp_path_factory):
    """Keep test sweeps out of the developer's real `generated/egt/`.

    The task module resolves the output root at call time from
    `egt.pipeline.DEFAULT_OUT_ROOT`, so patching it there redirects the
    artefacts without changing the request schema.
    """
    import pd_runner.api.egt_task as egt_task

    original = egt_task.DEFAULT_OUT_ROOT
    egt_task.DEFAULT_OUT_ROOT = tmp_path_factory.mktemp("egt_api")
    yield
    egt_task.DEFAULT_OUT_ROOT = original


@pytest.fixture(scope="module")
def client():
    return TestClient(app)


def _sweep(client, **overrides) -> dict:
    """POST a sweep and return the finished job payload."""
    body = {
        "zoo": "default",
        "ts": "1.0",
        "alphas": "0.5",
        "stages": "ess",
        "render": False,
    }
    body.update(overrides)
    res = client.post("/egt/sweep", json=body)
    assert res.status_code == 202
    job_id = res.json()["job_id"]
    return client.get(f"/egt/sweep/{job_id}").json()


# --------------------------------------------------------------------------
# Metadata
# --------------------------------------------------------------------------


def test_stages_endpoint_lists_stages_in_dependency_order(client):
    data = client.get("/egt/stages").json()
    assert [s["key"] for s in data["stages"]] == [
        "ess", "invasion", "faces", "nash", "replicator", "moran",
    ]


def test_every_stage_has_a_human_label(client):
    """A stage added to STAGES without a label must not break the endpoint."""
    data = client.get("/egt/stages").json()
    for stage in data["stages"]:
        assert stage["label"], f"{stage['key']} has no label"


def test_ess_is_marked_required(client):
    """ii.a writes the numeric matrix the others read, so it cannot be skipped."""
    data = client.get("/egt/stages").json()
    required = {s["key"] for s in data["stages"] if s["required"]}
    assert required == {"ess"}


def test_stages_endpoint_exposes_default_alphas(client):
    data = client.get("/egt/stages").json()
    assert data["default_alphas"][0] == 0.0
    assert data["default_alphas"][-1] == 1.0


def test_zoo_dropdown_source_is_shared_with_tau(client):
    """The UI fills both cards from /tau/zoos, so a new zoo appears in both."""
    data = client.get("/tau/zoos").json()
    keys = {z["key"] for z in data["zoos"]}
    assert {"default", "enlarged"} <= keys
    assert data["default"] in keys


# --------------------------------------------------------------------------
# Running a sweep
# --------------------------------------------------------------------------


def test_sweep_runs_and_reports_results(client):
    job = _sweep(client)
    assert job["status"] == "done"
    assert job["error"] is None

    result = job["egt_result"]
    assert result["zoo"] == "default"
    assert result["n_grid_points"] == 1
    assert result["n_distinct_matrices"] == 1
    assert result["ok"] is True
    assert result["runs"][0]["stages"]["ess"]["ok"] is True


def test_sweep_reports_dedup(client):
    """Two α values at t=1 give one matrix — the anchor theorem as dedup."""
    job = _sweep(client, alphas="0.3,0.8")
    result = job["egt_result"]
    assert result["n_grid_points"] == 2
    assert result["n_distinct_matrices"] == 1
    assert result["dedup_saved"] == 1
    assert result["runs"][0]["n_grid_points"] == 2


def test_sweep_accepts_both_zoos(client):
    for zoo in ("default", "enlarged"):
        job = _sweep(client, zoo=zoo)
        assert job["status"] == "done"
        assert job["egt_result"]["zoo"] == zoo


def test_sweep_honours_stage_selection(client):
    job = _sweep(client, stages="ess,invasion")
    stages = job["egt_result"]["runs"][0]["stages"]
    assert set(stages) == {"ess", "invasion"}


def test_sweep_reports_provenance(client):
    """The provenance flag is always reported. The default zoo has been fully
    proven since 2026-08-25 (its last stipulation, (PrudentBot, CupodBot), became
    a theorem), so it reads True; a stipulated zoo would read False."""
    job = _sweep(client)
    assert job["egt_result"]["runs"][0]["is_fully_proven"] is True


# --------------------------------------------------------------------------
# Failure paths — a bad request must fail loudly, not silently no-op
# --------------------------------------------------------------------------


def test_unknown_zoo_fails_with_the_valid_keys(client):
    job = _sweep(client, zoo="nope")
    assert job["status"] == "failed"
    assert "unknown zoo" in job["error"]
    assert "default" in job["error"]


def test_unparseable_alphas_fails(client):
    job = _sweep(client, alphas="abc")
    assert job["status"] == "failed"
    assert "phases" in job["error"]


def test_unparseable_ts_fails(client):
    job = _sweep(client, ts="1.0,xyz")
    assert job["status"] == "failed"
    assert "ts must be" in job["error"]


def test_empty_stage_selection_fails(client):
    job = _sweep(client, stages="  ")
    assert job["status"] == "failed"
    assert "at least one stage" in job["error"]


def test_unknown_stage_is_reported_without_losing_good_stages(client):
    """A bad stage name fails that stage; the valid ones still ran."""
    job = _sweep(client, stages="ess,bogus")
    assert job["status"] == "failed"
    assert job["egt_result"] is not None
    stages = job["egt_result"]["runs"][0]["stages"]
    assert stages["ess"]["ok"] is True
    assert stages["bogus"]["ok"] is False
    assert "unknown stage" in stages["bogus"]["error"]


def test_missing_job_is_404(client):
    assert client.get("/egt/sweep/not-a-real-job").status_code == 404


def test_alphas_phases_keyword_is_accepted(client):
    """'phases' is a documented keyword, not a parse error."""
    job = _sweep(client, alphas="phases", stages="ess")
    assert job["status"] == "done"
    # One α per behavioral phase; at t=1 the mass is a point mass.
    assert job["egt_result"]["n_grid_points"] >= 2

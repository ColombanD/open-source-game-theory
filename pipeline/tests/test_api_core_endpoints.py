"""The web API's endpoints over the CORE layer (`/matrix`, `/tau/zoos`, `/tau/report`, the EGT
run mount): the endpoint tests that used to sit beside the core tests in `app/tests/`, moved
here with the API. The core behaviour they exercise is tested in `app/tests/`; these check
the HTTP surface (query validation, the source/floor-policy plumbing, the UI toggles).
"""

from __future__ import annotations

from pathlib import Path

import pytest
from fastapi.testclient import TestClient

from pd_runner import settings
from pd_runner.tau.def4_theorems import SPRIME_RECORDED_DIVERGENCES


def _client() -> TestClient:
    from pd_pipeline.api.main import app

    return TestClient(app)


# ── the matrix and tau endpoints (moved from app/tests/test_cell_source.py) ────────────────────────────────────────────────────────────────


@pytest.fixture(scope="module")
def client():
    from pd_pipeline.api.main import app

    return TestClient(app)


@pytest.mark.parametrize("source", ["engine", "sprime"])
def test_matrix_endpoint_takes_a_source(client, source) -> None:
    r = client.get(f"/matrix?source={source}")
    assert r.status_code == 200
    body = r.json()
    assert body["source"] == source and body["floor_policy"] == settings.FLOOR_POLICY
    assert body["rows"][0][0] == "Outcome Matrix"
    marks = {e["mark"] for e in body["legend"]}
    assert {"‡", "≠"} <= marks
    if source == "sprime":
        assert body["floors"] == 29 and body["flips"] == 13   # 30 floor rows, Cupod×Prudent both ways
        d = body["details"]["DBot|DupocBot"]
        assert d["floor"] and d["provenance"] == "floor_dichotomy"
    else:
        assert body["floors"] == 0 and body["flips"] == 0


def test_matrix_endpoint_default_and_validation(client) -> None:
    assert client.get("/matrix").json()["source"] == settings.CELL_SOURCE
    r = client.get("/matrix?source=bogus")
    assert r.status_code == 400 and "unknown cell source" in r.json()["detail"]
    r = client.get("/tau/zoos?source=sprime")
    assert r.status_code == 200
    zoos = {z["key"]: z for z in r.json()["zoos"]}
    body = zoos["body"]
    assert body["floor_pairs"] == 4
    # Phase 4: kernel backing comes from the S' row file (full ⇒ backed; partial ⇒ a
    # coverage below 1 with the theorem / floor-dichotomy bit counts)
    assert body["kernel_backed"] is (body["kernel_coverage"] == 1.0)
    assert set(body["kernel_bits"]) == {"theorem", "floor_dichotomy"}
    engine_body = client.get("/tau/zoos?source=engine").json()["zoos"][0]
    assert engine_body["kernel_backed"] is True and engine_body["kernel_coverage"] == 1.0
    assert engine_body["kernel_bits"]["floor_dichotomy"] == 0
    r = client.get("/tau/report?zoo=body&alphas=0.5&source=sprime&floor_policy=restrict_zoo")
    assert r.status_code == 409 and "FLOOR" in r.json()["detail"]


def test_ui_ships_the_source_toggle_and_marks() -> None:
    html = (Path(__file__).parents[1] / "src" / "pd_pipeline" / "api" / "static"
            / "index.html").read_text(encoding="utf-8")
    assert 'name="matrix-source"' in html and "matrixQuery()" in html
    assert "mx-floor" in html and "mx-flip" in html


def test_tau_report_endpoint() -> None:
    """`GET /tau/report` serves the report fresh; bad alphas fail loudly."""
    client = _client()
    from pd_runner.tau.report import _SLIDER_ALPHAS, _SLIDER_TRANSPARENCIES

    n_a, n_t = len(_SLIDER_ALPHAS), len(_SLIDER_TRANSPARENCIES)
    page = client.get("/tau/report?alphas=0.5")
    assert page.status_code == 200
    assert page.headers["content-type"].startswith("text/html")
    assert "TauBots" in page.text
    assert page.text.count("<svg") == 3 * (2 + 2 * n_a + n_t + n_a * n_t) + n_a
    # top + charts 2, 3, 3b, 4
    assert page.text.count('class="alpha-slider"') == 5
    assert page.text.count('class="t-slider"') == 2  # charts 3b, 4b
    assert 'name="family"' in page.text  # σ-family selector

    assert client.get("/tau/report?alphas=abc").status_code == 400
    assert client.get("/tau/report?alphas=,").status_code == 400

    # The UI carries the trigger.
    index = client.get("/")
    assert "openTauReport" in index.text and "Run tau analysis" in index.text


def test_tau_zoos_endpoint_reports_coverage() -> None:
    """`GET /tau/zoos?source=sprime` reports the kernel backing of every zoo: coverage,
    the theorem / floor-dichotomy bit counts, the recorded divergences."""
    zoos = {z["key"]: z for z in _client().get("/tau/zoos?source=sprime").json()["zoos"]}
    body = zoos["body+twins+natives"]
    assert body["total"] and 0 < body["kernel_coverage"] <= 1
    assert body["kernel_backed"] is (body["kernel_coverage"] == 1.0)
    bits = body["kernel_bits"]
    # coverage counts STATED bits: the consulted ones plus the recorded divergences
    assert (bits["theorem"] + bits["floor_dichotomy"] + body["kernel_recorded"]
            == round(body["kernel_coverage"] * 196))
    if body["kernel_backed"]:
        dropped = 196 - bits["theorem"] - bits["floor_dichotomy"]
        assert dropped in (0, len(SPRIME_RECORDED_DIVERGENCES))
        assert body["kernel_recorded"] == dropped
        assert bits == {"theorem": 155 - dropped, "floor_dichotomy": 41}


def test_api_serves_runs_from_the_same_anchored_root():
    """The static mount and the sweep output must agree on one directory."""
    from pd_pipeline.api.main import _EGT_RUNS_DIR
    from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT

    assert _EGT_RUNS_DIR == DEFAULT_OUT_ROOT / "runs"

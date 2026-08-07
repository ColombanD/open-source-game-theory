"""Schema-pinning tests for the Nash stage's output files."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest

from src.nash.io import EQUILIBRIA_FIELDS, INDEX_CSV_HEADER, append_index_csv


def _latest_run_dir(repo_root: Path) -> Path:
    """Resolve `results/nash/latest` symlink to its target run directory."""
    latest = repo_root / "results" / "nash" / "latest"
    if not latest.exists():
        pytest.skip(
            "results/nash/latest does not exist; run `python -m src.nash.cli` first"
        )
    return latest.resolve()


def test_equilibria_jsonl_schema(tmp_path):
    repo = Path(__file__).resolve().parent.parent
    run_dir = _latest_run_dir(repo)
    path = run_dir / "equilibria.jsonl"
    assert path.exists()
    with open(path) as f:
        for line in f:
            rec = json.loads(line)
            assert set(rec.keys()) == set(EQUILIBRIA_FIELDS), (
                f"record keys: {sorted(rec.keys())} vs schema: {sorted(EQUILIBRIA_FIELDS)}"
            )
            # Soft type checks on a few key fields.
            assert isinstance(rec["index"], int)
            assert isinstance(rec["support_row"], list)
            assert isinstance(rec["xi_rational"], list)
            assert isinstance(rec["u_rational"], str) and "/" in rec["u_rational"]
            assert rec["classification"] in ("symmetric", "asymmetric")
            assert isinstance(rec["component_id"], int)
            assert isinstance(rec["touches_suspect_cell"], bool)


def test_provenance_json_schema():
    repo = Path(__file__).resolve().parent.parent
    run_dir = _latest_run_dir(repo)
    with open(run_dir / "provenance.json") as f:
        prov = json.load(f)
    expected_keys = {
        "run_id", "timestamp_utc", "input_csv_path", "input_csv_sha256",
        "config_path", "config_resolved", "bot_names", "payoff_shift",
        "library_versions", "methods_used", "iterated_dominance",
        "n_extreme_NE", "n_components", "n_pure_NE_direct",
        "n_pure_NE_in_method2_output", "cross_check_libraries_agree",
        "wallclock_seconds",
    }
    assert expected_keys <= set(prov.keys()), (
        f"missing: {expected_keys - set(prov.keys())}"
    )
    assert prov["cross_check_libraries_agree"] is True


def test_nash_components_json_references_valid_indices():
    repo = Path(__file__).resolve().parent.parent
    run_dir = _latest_run_dir(repo)
    with open(run_dir / "nash_components.json") as f:
        comps = json.load(f)
    with open(run_dir / "equilibria.jsonl") as f:
        valid_indices = {json.loads(line)["index"] for line in f}
    for c in comps["components"]:
        for idx in c["extreme_NE_indices"]:
            assert idx in valid_indices


def test_index_csv_has_documented_header(tmp_path):
    """Synthetic round-trip; the real INDEX.csv may have many rows."""
    p = tmp_path / "INDEX.csv"
    append_index_csv(
        p,
        timestamp="20260101T000000Z", short_hash="aaaaaaaaaaaa",
        run_id="20260101T000000Z_aaaaaaaaaaaa",
        n_extreme_NE=1, n_components=1,
        b=3.0, c=1.0, undefined_resolution="(C, D)",
        pygambit_version="16.6.0", lrsnash_version_str="lrsnash:test",
    )
    with open(p) as f:
        rows = list(csv.reader(f))
    assert tuple(rows[0]) == INDEX_CSV_HEADER


def test_assumptions_json_records_payoff_shift_and_versions():
    repo = Path(__file__).resolve().parent.parent
    run_dir = _latest_run_dir(repo)
    with open(run_dir / "assumptions.json") as f:
        a = json.load(f)
    assert a["stage"] == "nash_equilibria"
    assert a["method"] == "method2_polytope_vertex_enumeration"
    assert set(a["libraries_used"]) == {"pygambit", "lrsnash"}
    assert "c_shift" in a["payoff_shift"]
    assert "pygambit" in a["library_versions"]
    assert "lrsnash" in a["library_versions"]

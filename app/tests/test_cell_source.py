"""The cell-source switch (`SPRIME_SOURCE_OF_TRUTH.md` §1.3): PA-`S'` as the app's
ground truth, the engine as the comparison.

Runs against the committed ledger-derived SAMPLE export and, when it exists, the REAL
export `app/generated/sprime_outcome_theorems.json` (parametrized `sprime_export`;
the real one is skipped if absent). The engine-parity golden
(`tests/fixtures/engine_matrix_golden.json`) was snapshotted from the engine export
BEFORE the switch landed, so `source="engine"` must reproduce it byte for byte.
"""

from __future__ import annotations

import dataclasses
import json
import os
import subprocess
from pathlib import Path

import pytest
from fastapi.testclient import TestClient

from pd_runner import settings
from pd_runner.eval import outcome_matrix as om
from pd_runner.eval.outcome_matrix import (
    PAPER_BASE_BOTS,
    SPRIME_TWIN_BASE,
    _theorems_from_export,
    build_outcome_details,
    build_outcome_matrix,
    diff_sources,
    matrix_rows,
    scan_outcome_theorems,
)
from pd_runner.tau.matrix import (
    PAPER_BODY_SUB_ZOO,
    PAPER_TWINS_SUB_ZOO,
    ZOOS,
    load_tau_matrix,
)

_FIXTURES = Path(__file__).parent / "fixtures"
_GOLDEN = _FIXTURES / "engine_matrix_golden.json"
SPRIME_SAMPLE_EXPORT = _FIXTURES / "sprime_outcome_theorems.sample.json"
SPRIME_REAL_EXPORT = Path(__file__).parents[1] / "generated" / "sprime_outcome_theorems.json"


def _fixture_builder():
    """`tests/fixtures/make_sprime_fixture.build` (tests/ is not a package)."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "make_sprime_fixture", _FIXTURES / "make_sprime_fixture.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.build

_EXPORTS = [
    pytest.param(SPRIME_SAMPLE_EXPORT, id="sample"),
    pytest.param(
        SPRIME_REAL_EXPORT, id="real",
        marks=pytest.mark.skipif(
            not SPRIME_REAL_EXPORT.exists(),
            reason="sprime_outcome_theorems.json not generated yet "
                   "(run `lake exe export_sprime_outcomes` in arith/)"),
    ),
]


@pytest.fixture(params=_EXPORTS)
def sprime_export(request, monkeypatch) -> Path:
    """Point the `sprime` source at one of the two documents for the test."""
    monkeypatch.setitem(om._EXPORT_FILES, "sprime", request.param)
    return request.param


# ── (a) engine parity ──────────────────────────────────────────────────────────


def test_engine_matrix_reproduces_the_pre_switch_golden() -> None:
    golden = json.loads(_GOLDEN.read_text(encoding="utf-8"))
    bots, cells = build_outcome_matrix(source="engine")
    assert matrix_rows(bots, cells) == golden["matrix_rows"]
    theorems = scan_outcome_theorems(source="engine")
    keys = set(golden["theorems"][0])
    snapshot = [
        json.loads(json.dumps({k: v for k, v in dataclasses.asdict(t).items() if k in keys}))
        for t in theorems
    ]
    assert snapshot == golden["theorems"]
    # The new fields are inert on the engine source.
    assert {t.provenance for t in theorems} == {"engine"}
    assert all(t.hinge == "" and t.dichotomy == "" and t.twin_of == "" for t in theorems)
    assert not any(m in v for v in cells.values() for m in ("‡", "≠"))


def test_engine_export_digest_path_is_unchanged(tmp_path) -> None:
    """An engine document never hashes a `floors` key, even if one is present."""
    doc = json.loads(om._EXPORT_FILES["engine"].read_text(encoding="utf-8"))
    doc["floors"] = [{"name": "bogus"}]
    forged = tmp_path / "outcome_theorems.json"
    forged.write_text(json.dumps(doc), encoding="utf-8")
    assert len(_theorems_from_export(forged)) == len(doc["theorems"])


# ── (b) the default ────────────────────────────────────────────────────────────


def test_default_source_is_sprime_when_env_is_unset() -> None:
    env = {k: v for k, v in os.environ.items() if k not in ("PD_CELL_SOURCE", "PD_FLOOR_POLICY")}
    out = subprocess.run(
        ["python", "-c", "from pd_runner import settings; "
                         "print(settings.CELL_SOURCE, settings.FLOOR_POLICY)"],
        capture_output=True, text=True, env=env, check=True,
    )
    assert out.stdout.split() == ["sprime", "engine_side"]


def test_env_override_and_validation() -> None:
    env = dict(os.environ, PD_CELL_SOURCE="engine", PD_FLOOR_POLICY="restrict_zoo")
    out = subprocess.run(
        ["python", "-c", "from pd_runner import settings; "
                         "print(settings.CELL_SOURCE, settings.FLOOR_POLICY)"],
        capture_output=True, text=True, env=env, check=True,
    )
    assert out.stdout.split() == ["engine", "restrict_zoo"]
    bad = subprocess.run(
        ["python", "-c", "from pd_runner import settings"],
        capture_output=True, text=True, env=dict(os.environ, PD_CELL_SOURCE="foo"),
    )
    assert bad.returncode != 0 and "PD_CELL_SOURCE='foo'" in bad.stderr
    with pytest.raises(ValueError, match="unknown cell source"):
        settings.resolve_source("foo")
    with pytest.raises(ValueError, match="unknown floor policy"):
        settings.resolve_floor_policy("foo")


def test_missing_sprime_export_is_an_error_not_an_empty_matrix(tmp_path, monkeypatch) -> None:
    monkeypatch.setitem(om._EXPORT_FILES, "sprime", tmp_path / "absent.json")
    with pytest.raises(FileNotFoundError, match="export_sprime_outcomes"):
        scan_outcome_theorems(source="sprime")
    with pytest.raises(FileNotFoundError):
        load_tau_matrix(source="sprime")


# ── the S' document itself ─────────────────────────────────────────────────────


def test_sprime_document_shape(sprime_export) -> None:
    doc = json.loads(sprime_export.read_text(encoding="utf-8"))
    assert doc["schema_version"] == 1 and doc["system"] == "sprime"
    assert doc["companions"] == []
    for row in doc["theorems"]:
        assert row["provenance"] == "sprime" and row["fuel_pad"] == 0
        assert row["staggered"] is False
        assert row["budget_regime"] in ("nobudget", "universal", "eventual")
    for row in doc["floors"]:
        assert row["provenance"] == "floor_dichotomy"
        assert row["budget_regime"] == "eventual" and row["fuel_pad"] == 0
        assert row["pair"] is not None and row["dichotomy"].startswith("dich_")
        assert row["name"].endswith("_floor") and row["hinge"]


def test_sprime_cells_have_their_provenance(sprime_export) -> None:
    cells = scan_outcome_theorems(source="sprime")
    by_prov = {}
    for t in cells:
        by_prov.setdefault(t.provenance, []).append(t)
    assert set(by_prov) == {"sprime", "floor_dichotomy"}
    # 107 engine-cell statements + the 11 S'-only DupocTrollBot cells + the 10 S'-only DIMDID cells (2026-10-13);
    # 26 floors + DupocTrollBot's CIMCIC floor + DIMDID's three.
    assert len(by_prov["sprime"]) == 128 and len(by_prov["floor_dichotomy"]) == 30
    for f in by_prov["floor_dichotomy"]:
        assert f.is_floor and f.hinge and f.dichotomy == f"dich_{f.left_bot}_vs_{f.right_bot}"
        assert f.shape == "threshold" and f.budget_regime == "eventual"
    # `restrict_zoo` drops the floors and nothing else.
    assert len(scan_outcome_theorems(source="sprime", floor_policy="restrict_zoo")) == 128


def test_sprime_digest_covers_the_floors(sprime_export, tmp_path) -> None:
    doc = json.loads(sprime_export.read_text(encoding="utf-8"))
    doc["floors"][0]["pair"] = ["C", "C"] if doc["floors"][0]["pair"] != ["C", "C"] else ["D", "D"]
    forged = tmp_path / "sprime_outcome_theorems.json"
    forged.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
    with pytest.raises(ValueError, match="source_digest mismatch.*export_sprime_outcomes"):
        _theorems_from_export(forged)


def test_sprime_twin_rows_are_aliased_to_engine_bots(sprime_export) -> None:
    """Hand-template twins (`Just7`, `CupodTroll7`, …) never surface as bots."""
    cells = scan_outcome_theorems(source="sprime")
    bots = {b for t in cells for b in (t.left_bot, t.right_bot)}
    assert not bots & set(SPRIME_TWIN_BASE)
    aliased = [t for t in cells if t.twin_of]
    for t in aliased:
        assert t.name != f"outcome_{t.left_bot}_vs_{t.right_bot}"  # name kept as exported
        assert all(x in SPRIME_TWIN_BASE for x in t.twin_of.split(", "))
    doc = json.loads(sprime_export.read_text(encoding="utf-8"))
    twin_rows = [r for r in doc["theorems"]
                 if r["left_bot"] in SPRIME_TWIN_BASE or r["right_bot"] in SPRIME_TWIN_BASE]
    if twin_rows:  # an export from before the twins were retired (2026-10-02)
        assert {t.name for t in aliased} <= {r["name"] for r in twin_rows}
        by_pair = om.index_by_ordered_pair(cells)
        # The two paper-zoo pairs that exist ONLY under twin names reach the matrix.
        assert by_pair.get(("CupodTrollBot", "CupodBot")).twin_of == "CupodTroll7"
        assert by_pair.get(("DIMCID", "CupodTrollBot")).twin_of == "CupodTroll7"
    elif sprime_export == SPRIME_REAL_EXPORT:
        # Since 2026-10-02 the real export names engine bots only (the last twins were
        # re-proved on `JustBot`/`CupodTrollBot`): the aliasing is dormant.
        assert not aliased
        by_pair = om.index_by_ordered_pair(cells)
        assert by_pair.get(("CupodTrollBot", "CupodBot")).twin_of == ""
        assert by_pair.get(("DIMCID", "CupodTrollBot")).twin_of == ""


def test_twin_alias_collision_with_a_different_value_raises(tmp_path) -> None:
    doc = _fixture_builder()()
    base = next(t for t in doc["theorems"] if t["name"] == "outcome_JustBot_vs_JustBot")
    twin = dict(base, name="outcome_Just7_vs_Just7", left_bot="Just7", right_bot="Just7",
                left="Just7 k", right="Just7 k",
                pair=["D", "D"] if base["pair"] != ["D", "D"] else ["C", "C"])
    doc["theorems"].append(twin)
    doc["theorems"].sort(key=lambda t: t["name"])
    rows = [json.dumps(t, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            for t in doc["theorems"] + doc["companions"] + doc["floors"]]
    doc["source_digest"] = str(om._fnv1a64("".join(rows)))
    forged = tmp_path / "sprime_outcome_theorems.json"
    forged.write_text(json.dumps(doc, ensure_ascii=False), encoding="utf-8")
    with pytest.raises(ValueError, match="twin that is not a twin"):
        _theorems_from_export(forged)


def test_sample_fixture_is_current() -> None:
    """The committed sample equals what the generator derives from the ledger."""
    assert json.loads(SPRIME_SAMPLE_EXPORT.read_text(encoding="utf-8")) == _fixture_builder()()


# ── the rendered matrix ────────────────────────────────────────────────────────


def test_sprime_matrix_marks_floors_and_flips(sprime_export) -> None:
    bots, cells = build_outcome_matrix(source="sprime")
    assert cells[("DBot", "DupocBot")] == "(C, D) ‡"          # a floor, engine-side value
    assert cells[("DupocBot", "DIMCID")] == "(D, D) ≠"        # the universal-cell flip
    assert cells[("CooperateBot", "DIMCID")] == "(C, D) ≠"
    assert cells[("CupodBot", "DupocBot")] == "(C, D)"        # the red cell agrees
    assert cells[("MirrorBot", "MirrorBot")] == "None"
    assert cells[("CupodBot", "OptimBot")] == ""              # excluded: no S' statement, no status
    assert sum("‡" in v for v in cells.values()) == 29       # 30 floor rows, Cupod×Prudent both ways
    assert sum("≠" in v for v in cells.values()) == 13
    # Engine statuses are the engine's curation — not rendered for S'.
    assert cells[("OBot", "WaryBot")] == ""
    marks = [m for m, _ in om.MATRIX_LEGEND]
    assert "‡" in marks and "≠" in marks


def test_sprime_details_and_notes(sprime_export) -> None:
    d = build_outcome_details(source="sprime")
    floor = d[("DBot", "DupocBot")]
    assert floor["floor"] and floor["provenance"] == "floor_dichotomy"
    assert floor["dichotomy"] == "dich_DupocBot_vs_DBot" and floor["hinge"]
    assert "‡ floor dichotomy dich_DupocBot_vs_DBot" in floor["note"]
    assert "bounded consistency" in floor["note"]
    flip = d[("DupocBot", "DIMCID")]
    assert flip["flips_engine"] == {"theorem": "outcome_DIMCID_vs_DupocBot", "pair": ("D", "C")}
    assert "≠ flips the engine: outcome_DIMCID_vs_DupocBot proves (D, C) in S" in flip["note"]
    assert "Provenance: PA-S'" in flip["note"]


def test_flip_marks_need_the_engine_export(sprime_export, tmp_path, monkeypatch) -> None:
    monkeypatch.setitem(om._EXPORT_FILES, "engine", tmp_path / "absent.json")
    bots, cells = build_outcome_matrix(source="sprime")
    assert not any("≠" in v for v in cells.values())
    assert any("‡" in v for v in cells.values())


# ── (c)/(d) the tau layer ──────────────────────────────────────────────────────


@pytest.mark.parametrize("zoo", ["body", "body+twins", "body+twins+natives", "critch8"])
def test_paper_zoos_are_total_on_sprime_under_engine_side(sprime_export, zoo) -> None:
    m = ZOOS[zoo].load(source="sprime", floor_policy="engine_side")
    assert m.source == "sprime" and m.floor_policy == "engine_side"
    assert m.is_fully_proven and not m.hypothetical_cells
    for r in m.bots:
        for c in m.bots:
            assert m.cell(r, c).row_action in ("C", "D")


def test_body_floor_cells_are_exactly_the_four(sprime_export) -> None:
    m = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime")
    assert m.has_floors
    assert set(m.floor_pairs) == {
        ("CupodTrollBot", "DupocBot"), ("DBot", "DupocBot"),
        ("DupocBot", "EBot"), ("CupodBot", "OBot"),
    }
    assert len(m.floor_cells) == 8
    for k in m.floor_cells:
        assert m.cell(*k).is_floor and m.cell(*k).hinge
    # body+twins: 13 unordered floor pairs (Cupod×Prudent carries a dichotomy in
    # each orientation, so 14 floor ROWS), 25 ordered cells (Prudent×Prudent once).
    tw = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    assert len(tw.floor_pairs) == 13 and len(tw.floor_cells) == 25
    assert ("PrudentBot", "PrudentBot") in tw.floor_cells


def test_restrict_zoo_fails_body_on_its_floors(sprime_export) -> None:
    with pytest.raises(ValueError) as exc:
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime", floor_policy="restrict_zoo")
    msg = str(exc.value)
    assert "not total (sprime)" in msg and "8 unproven ordered cell(s)" in msg
    assert "4 of the unordered pairs are S' FLOOR dichotomies" in msg
    for pair in ("('CupodBot', 'OBot')", "('CupodTrollBot', 'DupocBot')",
                 "('DBot', 'DupocBot')", "('DupocBot', 'EBot')"):
        assert pair in msg
    # A floor-free roster loads under restrict_zoo.
    m = load_tau_matrix(("CooperateBot", "DefectBot", "TitForTatBot"),
                        source="sprime", floor_policy="restrict_zoo")
    assert not m.has_floors and m.floor_policy == "restrict_zoo"


def test_sprime_flip_cells_and_dimcid_twin(sprime_export) -> None:
    from pd_runner.tau.signal import behavioral_twins

    m = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime")
    assert m.action("DIMCID", "DupocBot") == "D" and m.action("DIMCID", "CooperateBot") == "D"
    flips = {tuple(sorted(p)) for p in m.flip_cells}
    assert all("DIMCID" in p for p in flips) and len(flips) == 7
    # The decision the note asks the paper to own: DIMCID is DefectBot's twin in S'.
    assert ("DIMCID", "DefectBot") in {tuple(sorted(g)) for g in behavioral_twins(m)}
    engine = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="engine")
    assert engine.flip_cells == () and engine.action("DIMCID", "DupocBot") == "C"


def test_stipulation_cannot_shadow_a_floor(sprime_export) -> None:
    with pytest.raises(ValueError, match="already have proven theorems"):
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime",
                        hypothetical_cells={("DupocBot", "DBot"): ("C", "C")})


# ── (f) kernel rows ────────────────────────────────────────────────────────────


def test_kernel_backing_is_per_source(sprime_export, tmp_path, monkeypatch) -> None:
    """Phase 4: each source loads ITS OWN row file. The engine's rows never serve a S'
    matrix — with the S' row file absent the S' matrix carries no kernel rows and its
    test bits fall back to the S' cells (DIMCID defects), never to the engine's rows
    (where DIMCID cooperates with DupocBot)."""
    from pd_runner.tau import def4_theorems as d4

    assert ZOOS["body"].load(source="engine").is_kernel_backed
    rows_file = d4._TAU_EXPORT_FILES["sprime"]
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", tmp_path / "absent.json")
    m = ZOOS["body"].load(source="sprime")
    assert not m.is_kernel_backed and m.kernel_rows == {} and m.kernel_coverage == 0.0
    assert m.test_bit("DIMCID", "DupocBot") == "D"
    # with the S' rows present (conftest: the sample, or the real file) they are consulted
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", rows_file)
    m = ZOOS["body"].load(source="sprime")
    assert m.kernel_coverage > 0 and m.test_bit("DIMCID", "DupocBot") == "D"
    assert ZOOS["body"].load(source="engine").test_bit("DIMCID", "DupocBot") == "C"


def test_def4_certification_refuses_a_sprime_matrix_without_sprime_rows(
        sprime_export, tmp_path, monkeypatch) -> None:
    from pd_runner.tau import def4_theorems as d4
    from pd_runner.tau.compare import SourceMismatchError, certify
    from pd_runner.tau.def4_theorems import CONTROL_BOTS

    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", tmp_path / "absent.json")
    with pytest.raises(SourceMismatchError, match="no S' tau rows exist yet"):
        certify(load_tau_matrix(CONTROL_BOTS, source="sprime"), "control")
    assert certify(load_tau_matrix(CONTROL_BOTS, source="engine"), "control").passed


# ── (e) the source diff ────────────────────────────────────────────────────────


def test_diff_sources_over_the_paper_base_bots(sprime_export) -> None:
    diff = diff_sources()
    z = diff.zoo("paper12")
    assert z.bots == PAPER_BASE_BOTS and len(z.pairs) == 78
    assert len(z.flips) == 9 and all("DIMCID" in (p.left, p.right) for p in z.flips)
    assert len(z.floors) == 13          # unordered pairs carried as dichotomies
    assert len(z.floor_rows) == 14      # floor THEOREMS (Cupod×Prudent in both orientations)
    assert len(z.agreeing) == 56 and z.missing == ()
    for p in z.flips:
        assert p.engine_pair != p.sprime_pair and p.engine_theorem and p.sprime_theorem
    for p in z.floors:
        assert p.dichotomy.startswith("dich_") and p.hinge
    assert len(diff.zoo("body").floors) == 4 and len(diff.zoo("body").flips) == 7
    md = diff.render_markdown()
    assert "| paper12 | 12 | 78 | 56 | 9 | 13 (14) | 0 |" in md
    custom = diff_sources(("DupocBot", "DIMCID", "DBot"))
    assert [z.key for z in custom.zoos] == ["custom"]


def test_source_diff_cli_writes_the_report(sprime_export, tmp_path) -> None:
    from pd_runner.eval.source_diff import main

    out = tmp_path / "source_diff.md"
    diff = main(["--output", str(out)])
    assert out.exists() and "paper12" in out.read_text(encoding="utf-8")
    assert {z.key for z in diff.zoos} >= {"body", "paper12"}


# ── staleness / refresh ────────────────────────────────────────────────────────


def test_sprime_refresh_runs_lake_in_arith(monkeypatch, tmp_path) -> None:
    calls: list[tuple[list[str], Path]] = []

    def fake_run(cmd, cwd, capture_output, text, check):
        calls.append((cmd, Path(cwd)))
        return subprocess.CompletedProcess(cmd, 0, stdout="ok\n", stderr="")

    monkeypatch.setattr(om.subprocess, "run", fake_run)
    out = tmp_path / "sprime.json"
    om.refresh_export(source="sprime", export_file=out)
    assert [c[0] for c in calls] == [
        ["lake", "build", "--try-cache", "ArithSOutcomeCheck"],
        ["lake", "exe", "export_sprime_outcomes", str(out.resolve())],
    ]
    assert all(c[1].name == "arith" for c in calls)
    calls.clear()
    om.refresh_export(source="engine", export_file=out)
    assert calls[0][0] == ["lake", "build", "PrisonersDilemma", "OutcomeCheck"]
    assert calls[0][1].name == "engine" and calls[1][0][:3] == ["lake", "exe", "export_outcomes"]


def test_sprime_staleness_messages(tmp_path, monkeypatch) -> None:
    monkeypatch.setitem(om._EXPORT_FILES, "sprime", tmp_path / "absent.json")
    reason = om.export_staleness(source="sprime")
    assert reason and "export_sprime_outcomes" in reason
    monkeypatch.setitem(om._EXPORT_FILES, "sprime", SPRIME_SAMPLE_EXPORT)
    reason = om.export_staleness(source="sprime")
    # The sample predates any arith source change; only the mtime hint may fire.
    assert reason is None or "newer than the S' export" in reason or "tagged" in reason


# ── EGT provenance ─────────────────────────────────────────────────────────────


def test_payoff_matrix_carries_source_and_floors(sprime_export) -> None:
    from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix, payoff_matrix_from_tournament
    from pd_runner.egt.pipeline import RunPaths, cells_fingerprint, sweep_summary_name
    from pd_runner.tau.sweep import run_tournament

    sp = payoff_matrix_from_tau_matrix(ZOOS["body"].load(source="sprime"), zoo="body")
    en = payoff_matrix_from_tau_matrix(ZOOS["body"].load(source="engine"), zoo="body")
    assert sp.cell_source == "sprime" and en.cell_source == "engine"
    assert len(sp.floor_cells) == 8 and en.floor_cells == ()
    a = sp.assumptions()
    assert a["cell_source"] == "sprime" and a["n_floor_cells"] == 8
    assert ["DBot", "DupocBot"] in a["floor_cells"] and a["is_fully_proven"]
    assert en.assumptions()["cell_source"] == "engine"
    # Same zoo, different systems: never the same run directory (even for equal cells).
    assert cells_fingerprint(sp) != cells_fingerprint(en)
    assert RunPaths.for_matrix(en).name.startswith("body_t100_ana_")
    assert RunPaths.for_matrix(sp).name.startswith("body_sprime_t100_ana_")
    # The top-level summary keeps its family-only name; it CARRIES `cell_source`
    # and the report trusts it only for the system it renders.
    assert sweep_summary_name("behavioral") == "sweep_summary.json"
    assert sweep_summary_name("epsilon") == "sweep_summary_epsilon.json"
    m = ZOOS["body"].load(source="sprime")
    t = payoff_matrix_from_tournament(run_tournament(m, t=0.5, alpha=0.5), bots=m.bots,
                                      zoo="body", cell_source=m.source, floor_cells=m.floor_cells)
    assert t.cell_source == "sprime" and t.floor_cells == sp.floor_cells


# ── (g) the API ────────────────────────────────────────────────────────────────


@pytest.fixture(scope="module")
def client():
    from pd_runner.api.main import app

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
    html = (Path(__file__).parents[1] / "src" / "pd_runner" / "api" / "static"
            / "index.html").read_text(encoding="utf-8")
    assert 'name="matrix-source"' in html and "matrixQuery()" in html
    assert "mx-floor" in html and "mx-flip" in html

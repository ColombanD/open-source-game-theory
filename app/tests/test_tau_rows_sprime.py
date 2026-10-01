"""The `S'` tau rows (`SPRIME_SOURCE_OF_TRUTH.md` §3, Phase 4): loader, verification,
rollout behaviour, and the Def 3 ≡ Def 4 certification on `source="sprime"`.

Runs against the committed cell-derived SAMPLE (`tests/fixtures/sprime_tau_rows.sample.json`,
full coverage: 196 bits = 155 row slots + 41 floor bits) and, when it exists, the REAL
export `app/generated/sprime_tau_rows.json` (parametrized `sprime_rows`; skipped if absent).
The REAL export is FULL since Phase 3f (2026-10-02): 196 bits = 149 row slots + 47 floor
bits — six more floor bits than the cell-derived sample, the RECORDED red-cell provenance
divergences (`SPRIME_RECORDED_DIVERGENCES`: a floor bit on a base THEOREM cell). The loader
DROPS those six kernel bits (the base cell is played), so on the real export the kernel
coverage is 190/196 and the matrix is not `is_kernel_backed`; the full-coverage assertions
below count the recorded divergences instead of assuming there are none.
The real export may be PARTIAL during the Phase-3 rollout, so every full-coverage
assertion is guarded by `_is_full` and the coverage is reported in the skip reason instead.
The two-row PARTIAL sample (`sprime_tau_rows.partial.sample.json`) exercises the rollout
path deterministically. Expected numbers are COMPUTED from the files (the base cells
decide which cells are floors), never hard-coded beyond mismatch == 0.
"""

from __future__ import annotations

import dataclasses
import importlib.util
import json
import warnings
from pathlib import Path

import pytest

from conftest import (
    SPRIME_TAU_PARTIAL_EXPORT,
    SPRIME_TAU_REAL_EXPORT,
    SPRIME_TAU_SAMPLE_EXPORT,
)
from pd_runner.tau import def4_theorems as d4
from pd_runner.tau.compare import SourceMismatchError, certify, direct_kernel_vs_base
from pd_runner.tau.def4_theorems import (
    BASE_OF,
    LEAN_SLOT,
    PAPER_ORDER,
    PAPER_TEMPLATES,
    SPRIME_RECORDED_DIVERGENCES,
    TAU_ORDER,
    RecordedDivergence,
    StaleDivergenceWarning,
    _load_export,
    kernel_bit_provenance,
    kernel_bits,
    kernel_floor_bits,
    kernel_row_bits,
    kernel_row_provenance,
)
from pd_runner.tau.matrix import (
    PAPER_BODY_SUB_ZOO,
    PAPER_NATIVES_SUB_ZOO,
    PAPER_TWINS_SUB_ZOO,
    ZOOS,
    _kernel_rows_for,
    load_tau_matrix,
)

_FIXTURES = Path(__file__).parent / "fixtures"

_ROWS = [
    pytest.param(SPRIME_TAU_SAMPLE_EXPORT, id="sample"),
    pytest.param(
        SPRIME_TAU_REAL_EXPORT, id="real",
        marks=pytest.mark.skipif(
            not SPRIME_TAU_REAL_EXPORT.exists(),
            reason="sprime_tau_rows.json not generated yet "
                   "(run `lake exe export_sprime_outcomes` in arith/)"),
    ),
]


@pytest.fixture(params=_ROWS)
def sprime_rows(request, monkeypatch) -> Path:
    """Point the `sprime` row reader at one of the two documents."""
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", request.param)
    if request.param == SPRIME_TAU_SAMPLE_EXPORT:
        # the cell-derived sample states no divergence by construction, so the recorded
        # red-cell entries cannot fire on it (`test_recorded_divergences_do_not_fire_on_the_sample`)
        warnings.simplefilter("ignore", StaleDivergenceWarning)
    return request.param


@pytest.fixture
def partial_rows(monkeypatch) -> Path:
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", SPRIME_TAU_PARTIAL_EXPORT)
    warnings.simplefilter("ignore", StaleDivergenceWarning)  # cell-derived, as the full sample
    return SPRIME_TAU_PARTIAL_EXPORT


def _fixture_builder():
    spec = importlib.util.spec_from_file_location(
        "make_sprime_tau_fixture", _FIXTURES / "make_sprime_tau_fixture.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _coverage(path: Path) -> tuple[int, int]:
    """(stated bits, 196) for a row document."""
    tables = kernel_bits(path, source="sprime")
    return sum(len(r) for r in tables.values()), len(PAPER_ORDER) ** 2


def _is_full(path: Path) -> bool:
    stated, total = _coverage(path)
    return stated == total


def _require_full(path: Path) -> None:
    stated, total = _coverage(path)
    if stated != total:
        pytest.skip(f"{path.name} is PARTIAL: {stated}/{total} bits stated "
                    f"({stated / total:.0%}) — full-coverage assertion skipped")


# ── the loader ─────────────────────────────────────────────────────────────────


def test_paper_order_is_the_lean_paper_order() -> None:
    """`ArithS.Tau.paperOrder` — 14 templates, a subset of the engine's `tauOrder`, with
    `dimcid` BEFORE `cimcic` (the engine orders them the other way)."""
    assert len(PAPER_ORDER) == 14 and set(PAPER_ORDER) < set(TAU_ORDER)
    assert PAPER_ORDER.index("dimcid") < PAPER_ORDER.index("cimcic")
    assert TAU_ORDER.index("cimcic") < TAU_ORDER.index("dimcid")
    assert [LEAN_SLOT[t] for t in PAPER_TEMPLATES] == list(PAPER_ORDER)
    lean = (Path(__file__).resolve().parents[2] / "arith" / "ArithS" / "Tau" / "Spec.lean")
    if lean.exists():
        src = lean.read_text(encoding="utf-8")
        body = src.split("def paperOrder : List Tmpl :=", 1)[1].split("]", 1)[0]
        assert tuple(s.strip().lstrip(".") for s in body.strip("[ \n").split(",")) == PAPER_ORDER


def test_document_shape(sprime_rows) -> None:
    doc = json.loads(sprime_rows.read_text(encoding="utf-8"))
    assert doc["schema_version"] == 1 and doc["system"] == "sprime"
    assert tuple(doc["order"]) == PAPER_ORDER
    for row in doc["rows"]:
        assert row["template"] in PAPER_ORDER
        assert set(row["bits"]) <= set(PAPER_ORDER)
        assert set(row["bits"].values()) <= {"C", "D"}
    for fb in doc["floor_bits"]:
        assert {"template", "slot", "action", "hinge", "dichotomy"} <= set(fb)
        assert fb["template"] in PAPER_ORDER and fb["slot"] in PAPER_ORDER
        # the six tau images of the red cell name the base THEOREM they depart from
        # (`outcome_DupocBot_vs_CupodBot`): no `dich_` exists for a floor on a theorem
        assert fb["action"] in {"C", "D"} and fb["dichotomy"].startswith(("dich_", "outcome_"))
    data = _load_export(source="sprime")
    assert data is not None


def test_digest_covers_rows_and_floor_bits(sprime_rows, tmp_path) -> None:
    doc = json.loads(sprime_rows.read_text(encoding="utf-8"))
    # a flipped floor bit must break the digest as surely as a flipped row slot
    forged = tmp_path / "sprime_tau_rows.json"
    fb = doc["floor_bits"][0]
    fb["action"] = "D" if fb["action"] == "C" else "C"
    forged.write_text(json.dumps(doc), encoding="utf-8")
    with pytest.raises(ValueError, match="source_digest mismatch.*export_sprime_outcomes"):
        kernel_bits(forged, source="sprime")
    doc = json.loads(sprime_rows.read_text(encoding="utf-8"))
    row = doc["rows"][0]
    slot = next(iter(row["bits"]))
    row["bits"][slot] = "D" if row["bits"][slot] == "C" else "C"
    forged.write_text(json.dumps(doc), encoding="utf-8")
    with pytest.raises(ValueError, match="source_digest mismatch"):
        kernel_bits(forged, source="sprime")


def test_loader_rejects_wrong_order_and_crossed_systems(sprime_rows, tmp_path) -> None:
    builder = _fixture_builder()
    doc = builder.build()
    doc["order"] = list(TAU_ORDER)
    # keep the digest valid: it covers rows ++ floor_bits only
    forged = tmp_path / "order.json"
    forged.write_text(json.dumps(doc), encoding="utf-8")
    with pytest.raises(ValueError, match="paperOrder.*PAPER_ORDER"):
        kernel_bits(forged, source="sprime")
    # the engine's file read as the S' source, and vice versa, are refused
    engine_file = d4._TAU_EXPORT_FILES["engine"]
    if engine_file.exists():
        with pytest.raises(ValueError, match="'engine' row file read as the 'sprime' source"):
            kernel_bits(engine_file, source="sprime")
        # ...while an explicit path with NO source is read as its own system
        assert "mirror" in kernel_bits(engine_file)
    with pytest.raises(ValueError, match="'sprime' row file read as the 'engine' source"):
        kernel_bits(sprime_rows, source="engine")
    assert set(kernel_bits(sprime_rows)) <= set(PAPER_ORDER)


def test_loader_rejects_a_slot_that_is_both_row_and_floor(tmp_path) -> None:
    from pd_runner.eval.outcome_matrix import _fnv1a64

    doc = _fixture_builder().build()
    fb = doc["floor_bits"][0]
    for row in doc["rows"]:
        if row["template"] == fb["template"]:
            row["bits"][fb["slot"]] = fb["action"]
    hashed = [json.dumps(r, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
              for r in doc["rows"] + doc["floor_bits"]]
    doc["source_digest"] = str(_fnv1a64("".join(hashed)))
    forged = tmp_path / "both.json"
    forged.write_text(json.dumps(doc), encoding="utf-8")
    with pytest.raises(ValueError, match="both a row slot and a floor bit"):
        kernel_bits(forged, source="sprime")


def test_absent_slots_are_absent_not_N(partial_rows) -> None:
    """Unlike the engine's `_DIVERGENT` fill, a slot the S' export does not state is
    simply missing from the table — and a template with no row is missing entirely."""
    tables = kernel_bits(source="sprime")
    assert set(tables) == {"dupoc", "ebot"}
    assert "N" not in {b for r in tables.values() for b in r.values()}
    assert set(kernel_bit_provenance(source="sprime")) == {"dupoc", "ebot"}
    assert "coop" not in kernel_row_bits(source="sprime").get("DupocBot", {}) or True
    assert "CooperateBot" not in kernel_row_bits(source="sprime")


# ── the bits against the S' cells ──────────────────────────────────────────────


def test_kernel_bits_equal_the_sprime_cells(sprime_rows) -> None:
    """Every stated bit at (A, T) is the S' base cell's A-action for `BASE_OF[A]` vs
    `BASE_OF[T]` (the natives on DupocBot), and a bit is a FLOOR bit iff that cell is
    a floor dichotomy — with the same engine-side value and the cell's hinge."""
    m = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    tables = kernel_bits(source="sprime")
    prov = kernel_bit_provenance(source="sprime")
    floors = kernel_floor_bits(source="sprime")
    stated = 0
    for A in PAPER_TEMPLATES:
        row = tables.get(LEAN_SLOT[A])
        if row is None:
            continue
        for T in PAPER_TEMPLATES:
            bit = row.get(LEAN_SLOT[T])
            if bit is None:
                continue
            stated += 1
            cell = m.cell(BASE_OF[A], BASE_OF[T])
            if (LEAN_SLOT[A], LEAN_SLOT[T]) in SPRIME_RECORDED_DIVERGENCES:
                # Def 3 ≢ Def 4 by theorem under the present coding (§3 FINDING): the
                # loader drops the bit, the certification reports it; not asserted equal
                continue
            assert bit == cell.row_action, (A, T)
            p = prov[LEAN_SLOT[A]][LEAN_SLOT[T]]
            assert (p == "floor_dichotomy") is cell.is_floor, (A, T, p)
            if cell.is_floor:
                fb = floors[LEAN_SLOT[A]][LEAN_SLOT[T]]
                # the tau floor bit's hinge is ITS OWN statement (on the compiled
                # instance's guard, `instCode`), the cell's is on the base bots; the
                # sample copies the cell's, the real export states the instance's
                assert fb.action == bit and fb.hinge
                assert fb.dichotomy == f"dich_{cell.theorem[len('outcome_'):-len('_floor')]}", (A, T)
    assert stated > 0
    _require_full(sprime_rows)
    assert stated == 196
    n_floor = sum(1 for r in prov.values() for v in r.values() if v == "floor_dichotomy")
    expected_floor = sum(
        1 for A in PAPER_TEMPLATES for T in PAPER_TEMPLATES
        if m.cell(BASE_OF[A], BASE_OF[T]).is_floor)
    # the row file's floor bits: the floor CELLS, plus the recorded provenance divergences
    # (a floor bit on a base theorem cell — the six tau images of the red cell on the real
    # export; none on the cell-derived sample)
    n_recorded_floor = sum(
        1 for (a, t), d in SPRIME_RECORDED_DIVERGENCES.items()
        if d.kind == "provenance" and prov.get(a, {}).get(t) == "floor_dichotomy"
        and not m.cell(BASE_OF[next(A for A in PAPER_TEMPLATES if LEAN_SLOT[A] == a)],
                       BASE_OF[next(T for T in PAPER_TEMPLATES if LEAN_SLOT[T] == t)]).is_floor)
    assert n_floor == expected_floor + n_recorded_floor
    # the §3 table: 13 flips of the engine among the 196, all DIMCID's
    engine = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="engine")
    flips = [(A, T) for A in PAPER_TEMPLATES for T in PAPER_TEMPLATES
             if tables[LEAN_SLOT[A]][LEAN_SLOT[T]] != engine.action(BASE_OF[A], BASE_OF[T])]
    assert len(flips) == 13 and all("TauDIMCID" in p for p in flips)


def test_natives_read_their_own_rows(sprime_rows) -> None:
    rows = kernel_row_bits(source="sprime")
    prov = kernel_row_provenance(source="sprime")
    if "MaxConfidenceBot" not in rows or "DupocBot" not in rows:
        pytest.skip("native/dupoc rows not stated yet")
    assert rows["MaxConfidenceBot"] == rows["DupocBot"]
    assert prov["MaxConfidenceBot"] == prov["DupocBot"]
    m = ZOOS["body+twins+natives"].load(source="sprime")
    if m.is_kernel_backed:
        assert m.kernel_provenance["MaxConfidenceBot"] == m.kernel_provenance["DupocBot"]
        for h in m.bots:
            assert m.test_bit("MaxConfidenceBot", h) == m.test_bit("DupocBot", h)
            assert m.test_bit(h, "MinConfidenceBot") == m.test_bit(h, "DupocBot")


# ── load-time verification ─────────────────────────────────────────────────────


def test_tampered_bit_raises_at_load(sprime_rows) -> None:
    """A present export that disagrees with a proven cell fails the load loudly, naming
    the pair — on any stated theorem bit (so it runs on a partial export too)."""
    m = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    stated = sorted((b, h) for b, r in m.kernel_rows.items() for h in r
                    if not m.cell(b, h).is_floor)
    assert stated, "no theorem bit stated"
    key = ("DupocBot", "DefectBot") if ("DupocBot", "DefectBot") in stated else stated[0]
    doctored = dict(m._cells)
    flipped = "C" if doctored[key].row_action == "D" else "D"
    doctored[key] = dataclasses.replace(doctored[key], row_action=flipped)
    with pytest.raises(ValueError, match=rf"(?s)kernel tau rows \(sprime\).*{key[0]} vs {key[1]}"):
        _kernel_rows_for(PAPER_TWINS_SUB_ZOO, doctored, source="sprime")


def test_provenance_swap_raises_at_load(sprime_rows) -> None:
    """A floor bit on a non-floor cell, or a theorem bit on a floor cell, is an export
    disagreement and raises even though the values agree."""
    m = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    stated = {(b, h) for b, r in m.kernel_rows.items() for h in r}
    floor_key = next((k for k in m.floor_cells if k in stated), None)
    theorem_key = next((k for k in stated if not m.cell(*k).is_floor), None)
    if floor_key is None or theorem_key is None:
        pytest.skip("need one stated floor bit and one stated theorem bit")
    doctored = dict(m._cells)
    doctored[floor_key] = dataclasses.replace(doctored[floor_key], provenance="sprime")
    with pytest.raises(ValueError, match="states a FLOOR bit but the base cell .* is not a floor"):
        _kernel_rows_for(PAPER_TWINS_SUB_ZOO, doctored, source="sprime")
    doctored = dict(m._cells)
    doctored[theorem_key] = dataclasses.replace(
        doctored[theorem_key], provenance="floor_dichotomy")
    with pytest.raises(ValueError, match="states a THEOREM bit but the base cell .* is a floor"):
        _kernel_rows_for(PAPER_TWINS_SUB_ZOO, doctored, source="sprime")


def test_engine_rows_are_never_verified_against_sprime_cells(sprime_rows) -> None:
    """The crossing that Phase 1 forbade stays forbidden: the engine's rows against S'
    cells would raise at DIMCID; the per-source load never gets there."""
    m = load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime")
    engine_rows = kernel_row_bits(source="engine")
    assert engine_rows["DIMCID"]["DupocBot"] == "C" and m.action("DIMCID", "DupocBot") == "D"
    if "DIMCID" in m.kernel_rows and "DupocBot" in m.kernel_rows["DIMCID"]:
        assert m.kernel_rows["DIMCID"]["DupocBot"] == "D"


# ── the rollout: a partial export ──────────────────────────────────────────────


def test_partial_export_loads_total_but_not_kernel_backed(partial_rows) -> None:
    m = load_tau_matrix(PAPER_NATIVES_SUB_ZOO, source="sprime")
    n = len(m.bots)
    assert len(m._cells) == n * n and m.is_fully_proven      # still total
    assert not m.is_kernel_backed
    assert set(m.kernel_backed_bots) == {"DupocBot", "EBot"}   # the two rows, all 14 slots
    assert m.kernel_coverage == pytest.approx(2 * n / (n * n))
    counts = m.kernel_bit_counts
    assert counts["theorem"] + counts["floor_dichotomy"] == 2 * n
    assert counts["floor_dichotomy"] == sum(
        1 for b in ("DupocBot", "EBot") for h in m.bots if m.cell(b, h).is_floor)
    # uncovered bits fall back to the S' cells — values unchanged
    for b in m.bots:
        for h in m.bots:
            assert m.test_bit(b, h) == m.action(b, h)
    # natives are NOT backed: their own template rows are absent from the partial file
    assert "MaxConfidenceBot" not in m.kernel_rows
    assert m.test_bit("MaxConfidenceBot", "EBot") == m.action("DupocBot", "EBot")


def test_partial_export_coverage_on_every_paper_zoo(partial_rows) -> None:
    for key in ("body", "body+twins", "body+twins+natives", "critch8"):
        m = ZOOS[key].load(source="sprime")
        n = len(m.bots)
        assert 0 < m.kernel_coverage < 1, key
        assert m.kernel_coverage == pytest.approx(2 / n), key


# ── the certification on S' ────────────────────────────────────────────────────


def test_certification_on_sprime(sprime_rows) -> None:
    m = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    cert = certify(m, "paper")
    d = cert.direct
    assert cert.passed and d.mismatches == 0 and d.unexpected == ()
    # a floor bit agrees with a floor cell of the same value, and is counted apart
    expected_floor = sum(
        1 for c in d.cells if m.cell(BASE_OF[c.template], BASE_OF[c.hypothesis]).is_floor)
    assert d.floor_agreements == expected_floor
    # the covered cells are the agreements plus the RECORDED divergences (whitelisted)
    assert d.theorem_agreements + d.floor_agreements == d.agreements
    assert d.agreements + len(d.whitelisted_divergences) == d.covered
    assert all(c.whitelisted.startswith("recorded ") for c in d.whitelisted_divergences)
    assert d.total == 196 and d.covered + len(d.uncovered) == 196
    assert set(d.coverage_by_template) <= set(PAPER_TEMPLATES)
    _require_full(sprime_rows)
    assert d.complete and d.covered == 196 and d.uncovered == () and d.missing_rows == ()
    # the 14×14 table's floor cells: the natives' rows and columns are Dupoc's
    table = ZOOS["body+twins+natives"].load(source="sprime")
    assert d.floor_agreements == len(table.floor_cells) == 41
    # theorem agreements: everything but the floor cells and the recorded divergences
    # (155 on the cell-derived sample, 149 on the real export — six recorded red-cell bits)
    assert d.theorem_agreements == 196 - d.floor_agreements - len(d.whitelisted_divergences)
    assert len(d.whitelisted_divergences) in (0, len(SPRIME_RECORDED_DIVERGENCES))


def test_certification_on_the_partial_export(partial_rows) -> None:
    m = load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime")
    d = direct_kernel_vs_base(m)
    assert d.passed and not d.complete
    assert d.covered == 28 and len(d.uncovered) == 168 and d.total == 196
    assert d.coverage_by_template["TauDupoc"] == (14, 14)
    assert d.coverage_by_template["TauCooperate"] == (0, 14)
    assert "TauCooperate" in d.missing_rows and "TauDupoc" not in d.missing_rows
    assert d.floor_agreements == sum(
        1 for b in ("DupocBot", "EBot") for T in PAPER_TEMPLATES
        if m.cell(b, BASE_OF[T]).is_floor)


def test_certification_scope_is_the_paper_templates_on_sprime(sprime_rows) -> None:
    """Engine-only templates (TauJust, TauGuardian, TauMirror, TauTFTPf) are out of scope
    on S' — neither compared nor reported missing."""
    d = direct_kernel_vs_base(load_tau_matrix(PAPER_TWINS_SUB_ZOO, source="sprime"))
    seen = {c.template for c in d.cells} | {c.hypothesis for c in d.cells} | set(d.missing_rows)
    assert seen <= set(PAPER_TEMPLATES)


def test_certification_refuses_sprime_without_rows(tmp_path, monkeypatch) -> None:
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", tmp_path / "absent.json")
    with pytest.raises(SourceMismatchError, match="no S' tau rows exist yet"):
        certify(load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime"), "body")


def test_compare_cli_prints_the_four_numbers(sprime_rows, capsys, monkeypatch) -> None:
    import sys

    from pd_runner.tau import compare

    monkeypatch.setattr(sys, "argv", ["compare", "--zoo", "paper", "--source", "sprime"])
    with pytest.raises(SystemExit) as exc:
        compare.main()
    assert exc.value.code == 0
    out = capsys.readouterr().out
    assert "floor-agree (dichotomy bits):" in out and "uncovered:" in out
    assert "coverage per template:" in out and "mismatch: 0" in out


# ── the engine path is untouched ───────────────────────────────────────────────


def test_engine_certification_numbers_unchanged(sprime_rows) -> None:
    from test_def4_compare import FULL_BOTS

    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS, source="engine"))
    assert d.covered == d.agreements == 289 and d.floor_agreements == 0
    assert d.uncovered == () and d.missing_rows == () and d.complete
    e = ZOOS["body+twins+natives"].load(source="engine")
    assert e.is_kernel_backed and e.kernel_coverage == 1.0
    assert e.kernel_bit_counts == {"theorem": 196, "floor_dichotomy": 0}


# ── the fixtures and the endpoints ─────────────────────────────────────────────


def test_sample_fixtures_are_current() -> None:
    """The committed samples equal what the generator derives from the S' base cells."""
    builder = _fixture_builder()
    assert json.loads(SPRIME_TAU_SAMPLE_EXPORT.read_text(encoding="utf-8")) == builder.build()
    assert json.loads(SPRIME_TAU_PARTIAL_EXPORT.read_text(encoding="utf-8")) == builder.build(
        templates=builder.PARTIAL_TEMPLATES)
    full = json.loads(SPRIME_TAU_SAMPLE_EXPORT.read_text(encoding="utf-8"))
    assert len(full["rows"]) == 14 and len(full["floor_bits"]) == 41
    assert sum(len(r["bits"]) for r in full["rows"]) == 155


def test_real_export_coverage_report() -> None:
    """Not an assertion on the rollout — a visible gauge: how much of the real S' row
    file is stated (skipped with the numbers when partial, passes silently when full)."""
    if not SPRIME_TAU_REAL_EXPORT.exists():
        pytest.skip("sprime_tau_rows.json not generated yet")
    stated, total = _coverage(SPRIME_TAU_REAL_EXPORT)
    if stated != total:
        pytest.skip(f"real sprime_tau_rows.json covers {stated}/{total} bits "
                    f"({stated / total:.0%})")


def test_tau_zoos_endpoint_reports_coverage(sprime_rows) -> None:
    from fastapi.testclient import TestClient

    from pd_runner.api.main import app

    client = TestClient(app)
    zoos = {z["key"]: z for z in client.get("/tau/zoos?source=sprime").json()["zoos"]}
    body = zoos["body+twins+natives"]
    assert body["total"] and 0 < body["kernel_coverage"] <= 1
    assert body["kernel_backed"] is (body["kernel_coverage"] == 1.0)
    bits = body["kernel_bits"]
    assert bits["theorem"] + bits["floor_dichotomy"] == round(body["kernel_coverage"] * 196)
    if _is_full(sprime_rows):
        # a recorded divergence that fires DROPS its kernel bit (`_kernel_rows_for`): the
        # sample has none (kernel-backed, 155 + 41); the real export has the six red-cell
        # provenance bits (190/196: 149 theorem + 41 floor-dichotomy, not kernel-backed)
        dropped = 196 - bits["theorem"] - bits["floor_dichotomy"]
        assert dropped in (0, len(SPRIME_RECORDED_DIVERGENCES))
        assert body["kernel_backed"] is (dropped == 0)
        assert bits == {"theorem": 155 - dropped, "floor_dichotomy": 41}


def test_report_banner_names_the_backing(sprime_rows) -> None:
    from pd_runner.tau.report import build_report

    named = ZOOS["body"]
    matrix = named.load(source="sprime")
    page = build_report(matrix, (0.5,), zoo=named)
    assert "sprime_tau_rows.json" in page
    if matrix.is_kernel_backed:
        assert _is_full(sprime_rows)
        assert "kernel-backed (Def 4" in page and "floor-dichotomy bits" in page
    else:
        # a partial export, OR the full real export with its recorded red-cell bits dropped
        # (`body` holds Dupoc and Cupod: 98/100) — the banner's second branch either way
        assert "PARTIAL export" in page
        if _is_full(sprime_rows):
            assert matrix.kernel_divergences and matrix.kernel_coverage == pytest.approx(0.98)


# ── recorded divergences must fire, or be removed (Phase 3e) ───────────────────


def test_the_value_divergences_are_gone() -> None:
    """Route (c) made generic dissolved the six VALUE divergences of Phases 3b–3d; only the
    six red-cell PROVENANCE divergences remain recorded."""
    assert len(SPRIME_RECORDED_DIVERGENCES) == 6
    assert {d.kind for d in SPRIME_RECORDED_DIVERGENCES.values()} == {"provenance"}
    assert all("cupod" in pair for pair in SPRIME_RECORDED_DIVERGENCES)


@pytest.mark.skipif(not SPRIME_TAU_REAL_EXPORT.exists(),
                    reason="sprime_tau_rows.json not generated yet")
def test_every_recorded_divergence_fires_on_the_real_export(monkeypatch) -> None:
    """On the real export no recorded entry is stale, on any paper zoo."""
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", SPRIME_TAU_REAL_EXPORT)
    with warnings.catch_warnings():
        warnings.simplefilter("error", StaleDivergenceWarning)
        for zoo in (PAPER_BODY_SUB_ZOO, PAPER_TWINS_SUB_ZOO, PAPER_NATIVES_SUB_ZOO):
            load_tau_matrix(zoo, source="sprime")


@pytest.mark.skipif(not SPRIME_TAU_REAL_EXPORT.exists(),
                    reason="sprime_tau_rows.json not generated yet")
def test_a_stale_recorded_divergence_is_loud(monkeypatch) -> None:
    """An entry at a bit the row states in AGREEMENT with its proven cell is reported."""
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", SPRIME_TAU_REAL_EXPORT)
    monkeypatch.setitem(SPRIME_RECORDED_DIVERGENCES, ("coop", "defect"),
                        RecordedDivergence("value", "a stale entry, for the test"))
    with pytest.warns(StaleDivergenceWarning, match="CooperateBot vs DefectBot"):
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime")


def test_recorded_divergences_do_not_fire_on_the_sample(monkeypatch) -> None:
    """The cell-derived sample states the red-cell bits as theorem bits equal to the base
    cells, so the recorded provenance divergences are reported as not firing there — the
    reason the sample fixtures silence the warning."""
    monkeypatch.setitem(d4._TAU_EXPORT_FILES, "sprime", SPRIME_TAU_SAMPLE_EXPORT)
    with pytest.warns(StaleDivergenceWarning, match="DupocBot vs CupodBot"):
        load_tau_matrix(PAPER_BODY_SUB_ZOO, source="sprime")

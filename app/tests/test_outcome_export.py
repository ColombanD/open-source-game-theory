"""The Lean-side `@[outcome]` export — the structured replacement for regex scraping.

These are the checks that would have caught the historical `_HYP_RE` bug: the dagger flag
now comes from an elaborated type (a real `Prop` binder, or a structurally staggered budget
lambda), not from a binder-name convention.
"""
from __future__ import annotations

import json
import re

import pytest

from pd_runner.eval.outcome_matrix import (
    _EXPORT_FILE,
    _SHAPE_MAP,
    _theorems_from_export,
    scan_outcome_theorems,
)

# The export lands only once the Lean side has been built at least once. Until the
# migration completes it covers a subset, so these tests assert its INTERNAL consistency
# rather than a fixed count.
pytestmark = pytest.mark.skipif(
    not _EXPORT_FILE.exists(),
    reason="outcome_theorems.json not generated yet (run `lake exe export_outcomes`)",
)

_REGIMES = {"nobudget", "universal", "eventual"}
_ACTIONS = {"C", "D"}


def _doc() -> dict:
    return json.loads(_EXPORT_FILE.read_text(encoding="utf-8"))


def test_schema_version_is_pinned() -> None:
    assert _doc()["schema_version"] == 1


def test_every_regime_is_a_known_literal() -> None:
    for t in _doc()["theorems"]:
        assert t["budget_regime"] in _REGIMES, t
        assert t["budget_regime"] in _SHAPE_MAP, t


def test_pairs_are_literal_actions_or_null() -> None:
    for t in _doc()["theorems"]:
        if t["pair"] is None:
            continue  # a proven `= none`
        a, b = t["pair"]
        assert a in _ACTIONS and b in _ACTIONS, t


def test_names_agree_with_the_bots_in_the_statement() -> None:
    """The linter enforces this in Lean; assert it survives serialization.

    Nothing in the old regex world stopped `outcome_A_vs_B` from being a statement about
    some third bot — which would have put a wrong value in the matrix silently.
    """
    for t in _doc()["theorems"]:
        name = t["name"]
        core = name[len("llm_"):] if name.startswith("llm_") else name
        core = core[len("outcome_"):]
        left, right = core.split("_vs_")
        assert left == t["left_bot"], t
        assert right == t["right_bot"], t


def test_fuel_pad_is_a_nat() -> None:
    for t in _doc()["theorems"]:
        assert isinstance(t["fuel_pad"], int) and t["fuel_pad"] >= 0, t


def test_dagger_has_exactly_one_cause() -> None:
    """The dagger is `staggered` and nothing else — the linter rejects side hypotheses."""
    for t in _doc()["theorems"]:
        assert isinstance(t["staggered"], bool), t
        assert "side_conditions" not in t, t


def test_export_feeds_the_scan() -> None:
    """Every exported theorem reaches `scan_outcome_theorems` with a mapped shape."""
    exported = {t.name: t for t in _theorems_from_export()}
    assert exported, "export is present but empty"
    scanned = {t.name: t for t in scan_outcome_theorems()}
    for name, t in exported.items():
        assert name in scanned, f"{name} exported but missing from the scan"
        # The export is authoritative where it and the legacy regex overlap.
        assert scanned[name].pair == t.pair
        assert scanned[name].shape == t.shape
        assert scanned[name].staggered == t.staggered


def test_hand_edited_export_is_rejected(tmp_path) -> None:
    """A tampered export must not reach the matrix.

    The cells are machine-checked theorems; a JSON edited by hand is not. This test
    exists because the digest was originally computed but never VERIFIED — flipping a
    `pair` in the file silently rewrote a proven cell and every consumer believed it.
    """
    doc = _doc()
    assert doc["theorems"], "need at least one cell to tamper with"
    doc["theorems"][0]["pair"] = ["D", "D"]
    forged = tmp_path / "outcome_theorems.json"
    forged.write_text(json.dumps(doc), encoding="utf-8")

    with pytest.raises(ValueError, match="source_digest mismatch"):
        _theorems_from_export(forged)


def test_missing_digest_is_rejected(tmp_path) -> None:
    doc = _doc()
    doc.pop("source_digest", None)
    forged = tmp_path / "outcome_theorems.json"
    forged.write_text(json.dumps(doc), encoding="utf-8")

    with pytest.raises(ValueError, match="missing `source_digest`"):
        _theorems_from_export(forged)


def test_genuine_export_verifies() -> None:
    """The committed file's digest must match — else it is stale."""
    assert _theorems_from_export(_EXPORT_FILE)


def test_export_covers_every_tagged_theorem_on_disk() -> None:
    """The committed export must not be STALE relative to the Lean sources.

    The digest catches a TAMPERED export and the Lean census catches an untagged
    theorem, but neither notices an export that is merely BEHIND — migrate a batch,
    forget to re-run `lake exe export_outcomes`, and the matrix silently keeps serving
    the previous cell set. That surfaced once as `tau matrix is not total` in the EGT
    tests, which is a confusing way to learn you skipped a command.

    Anchored on the SOURCE TREE rather than a counter: `Check.lean` used to carry an
    `expecting <n>` literal, but that was the migration counter and has been retired
    (pinning the count taxed every correctly-tagged new theorem). Counting
    `@[outcome]` attributes on disk needs no bookkeeping to stay true.
    """
    theorems = _EXPORT_FILE.parents[2] / "engine" / "PrisonersDilemma" / "Theorems"
    if not theorems.is_dir():  # app-only checkout
        pytest.skip("engine sources not present")

    tagged_on_disk = sum(
        f.read_text(encoding="utf-8").count("@[outcome]")
        for f in theorems.rglob("vs_*.lean")
    )
    exported = len(_doc()["theorems"])
    assert exported == tagged_on_disk, (
        f"outcome_theorems.json has {exported} cells but {tagged_on_disk} theorems are "
        f"tagged `@[outcome]` on disk — re-run `lake exe export_outcomes` "
        f"(the export is stale)."
    )


def test_export_staleness_detects_a_lagging_file(tmp_path) -> None:
    """A count mismatch between `@[outcome]` on disk and the export is reported."""
    from pd_runner.eval.outcome_matrix import export_staleness

    theorems = tmp_path / "Theorems"
    (theorems / "A").mkdir(parents=True)
    (theorems / "A" / "vs_B.lean").write_text(
        "@[outcome]\ntheorem outcome_A_vs_B : True := trivial\n"
        "@[outcome]\ntheorem outcome_A_vs_C : True := trivial\n",
        encoding="utf-8",
    )
    export = tmp_path / "outcome_theorems.json"

    assert "missing" in export_staleness(export, theorems)

    export.write_text(json.dumps({"theorems": [{}]}), encoding="utf-8")
    reason = export_staleness(export, theorems)
    assert reason is not None and "1 cells" in reason and "2 theorems" in reason


def test_export_staleness_is_quiet_when_current(tmp_path) -> None:
    from pd_runner.eval.outcome_matrix import export_staleness

    theorems = tmp_path / "Theorems"
    (theorems / "A").mkdir(parents=True)
    (theorems / "A" / "vs_B.lean").write_text("@[outcome]\ntheorem x : True := trivial\n")
    export = tmp_path / "outcome_theorems.json"
    export.write_text(json.dumps({"theorems": [{}]}), encoding="utf-8")
    # The export was written AFTER the source, so no mtime hint fires either. (The tau
    # check is pointed at a non-directory so this stays about the base export.)
    assert export_staleness(export, theorems, tau_phase_dir=tmp_path / "no-tau") is None


def test_committed_export_is_not_stale() -> None:
    """The committed export passes the same check the UI shows (count + mtime)."""
    from pd_runner.eval.outcome_matrix import export_staleness

    theorems = _EXPORT_FILE.parents[2] / "engine" / "PrisonersDilemma" / "Theorems"
    if not theorems.is_dir():
        pytest.skip("engine sources not present")
    reason = export_staleness(_EXPORT_FILE, theorems)
    # The mtime hint is advisory (a checkout can touch files); the COUNT must agree.
    assert reason is None or "newer than the export" in reason, reason


# ── the tau rows export ────────────────────────────────────────────────────────

_TAU_EXPORT = _EXPORT_FILE.parent / "tau_rows.json"


@pytest.mark.skipif(not _TAU_EXPORT.exists(), reason="tau_rows.json not generated yet")
def test_tau_export_has_one_row_per_template() -> None:
    """The Lean census guarantees one `@[tau_row]` per `Tmpl`; the export carries it."""
    from pd_runner.tau.def4_theorems import TAU_ORDER, kernel_bits

    data = json.loads(_TAU_EXPORT.read_text(encoding="utf-8"))
    assert tuple(data["order"]) == TAU_ORDER
    assert sorted(r["template"] for r in data["rows"]) == sorted(TAU_ORDER)
    for r in data["rows"]:
        assert r["order"] in ("tauOrder", "tauOrderInit"), r
        assert set(r["bits"].values()) <= {"C", "D"}, r
    # The prefix row (τ(Mirror)) is the only one short of the full order, and the
    # reader fills its diagonal with "N".
    prefix = [r["template"] for r in data["rows"] if r["order"] == "tauOrderInit"]
    assert prefix == ["mirror"]
    assert kernel_bits()["mirror"]["mirror"] == "N"


@pytest.mark.skipif(not _TAU_EXPORT.exists(), reason="tau_rows.json not generated yet")
def test_hand_edited_tau_export_is_rejected(tmp_path) -> None:
    from pd_runner.tau.def4_theorems import kernel_bits

    data = json.loads(_TAU_EXPORT.read_text(encoding="utf-8"))
    row = data["rows"][0]
    slot = next(iter(row["bits"]))
    row["bits"][slot] = "D" if row["bits"][slot] == "C" else "C"
    forged = tmp_path / "tau_rows.json"
    forged.write_text(json.dumps(data), encoding="utf-8")
    with pytest.raises(ValueError, match="source_digest"):
        kernel_bits(forged)

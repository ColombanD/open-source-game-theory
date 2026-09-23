"""Tier A2 profile-builder tests — pure classification logic, no Lean required.

The load-bearing case is `phase_dependent`: a bot whose outcome changes with the
proof budget (WaryBot vs DefectBot is (C,D) at k=2,4 and (D,D) at k=16) must NOT
be reported as a stable action, because a downstream faithfulness check would
then flag a budget artifact as a mismatch.
"""

from __future__ import annotations

from pathlib import Path

import pytest

from pd_runner.eval.outcome_prepass import CellResult
from pd_runner.services.bot_profile import (
    CANONICAL_OPPONENTS,
    DEFAULT_BUDGETS,
    DEFAULT_JOBS,
    MAX_TOTAL_MEMORY_MB,
    PROFILE_MEMORY_MB,
    BotProfile,
    _classify,
    build_profile,
    staged_bot,
)


def _cell(right: str, k: int, status: str, outcome: str | None, note: str = "") -> CellResult:
    return CellResult(
        left="B", right=right, budget=k, fuel_d=k, fuel=64,
        status=status, outcome=outcome, note=note, seconds=1.0,
    )


def test_canonical_opponents_are_search_free() -> None:
    """All four canonical opponents must be non-searchers, else the sweep hits
    the both-searcher regime that is infeasible at k>2."""
    from pd_runner.eval.outcome_prepass import REGISTRY

    for opp in CANONICAL_OPPONENTS:
        assert REGISTRY[opp].guard is None, f"{opp} is a searcher"


def test_stable_cell() -> None:
    results = [_cell("DefectBot", k, "determined", "(D, D)") for k in (2, 4, 6, 16)]
    c = _classify("DefectBot", results)
    assert c.verdict == "stable"
    assert (c.my_action, c.opponent_action) == ("D", "D")
    assert c.transition_budgets == []


def test_phase_dependent_cell_is_not_reported_as_an_action() -> None:
    """The WaryBot-vs-DefectBot shape: (C,D) low-k, (D,D) high-k."""
    results = [
        _cell("DefectBot", 2, "determined", "(C, D)"),
        _cell("DefectBot", 4, "determined", "(C, D)"),
        _cell("DefectBot", 6, "determined", "(C, D)"),
        _cell("DefectBot", 16, "determined", "(D, D)"),
    ]
    c = _classify("DefectBot", results)
    assert c.verdict == "phase_dependent"
    assert c.my_action is None, "a phase-dependent cell must not claim a single action"
    assert c.transition_budgets == [16]
    assert "phase transition" in c.note


def test_undetermined_cell_keeps_the_reason() -> None:
    results = [
        _cell("MirrorBot", k, "undetermined", None, note="Löb boundary or budget floor")
        for k in (2, 4)
    ]
    c = _classify("MirrorBot", results)
    assert c.verdict == "undetermined"
    assert c.my_action is None
    assert "Löb boundary" in c.note


def test_partially_determined_cell_is_stable_on_the_determined_budgets() -> None:
    """One OOM among otherwise-agreeing budgets should not sink the cell."""
    results = [
        _cell("CooperateBot", 2, "determined", "(C, C)"),
        _cell("CooperateBot", 4, "determined", "(C, C)"),
        _cell("CooperateBot", 16, "oom", None, note="exceeded cap"),
    ]
    c = _classify("CooperateBot", results)
    assert c.verdict == "stable"
    assert c.my_action == "C"
    assert c.by_budget[16] is None


def test_profile_coverage_and_lookup() -> None:
    cells = tuple(
        _classify(opp, [_cell(opp, 2, "determined", "(C, C)")])
        for opp in ("CooperateBot", "MirrorBot")
    ) + (
        _classify("DefectBot", [_cell("DefectBot", 2, "undetermined", None, "floor")]),
    )
    p = BotProfile(bot_name="B", cells=cells, budgets=(2,))
    assert p.coverage == pytest.approx(2 / 3)
    assert p.cell("MirrorBot").my_action == "C"
    assert p.cell("DefectBot").my_action is None
    assert p.cell("NoSuchBot") is None
    assert p.actions_by_opponent() == {
        "CooperateBot": "C", "MirrorBot": "C", "DefectBot": None,
    }
    assert "B" in p.render()


def test_jobs_are_clamped_to_the_memory_ceiling(monkeypatch: pytest.MonkeyPatch) -> None:
    """`jobs × memory_mb` is what the machine sees. A caller asking for more
    parallelism than the ceiling allows must get fewer workers, not an OOM —
    this project has lost a machine to unbounded decFull sweeps three times."""
    seen: dict[str, int] = {}

    def fake_run_cells(cells, **kw):
        seen.update(jobs=kw["jobs"], memory_mb=kw["memory_mb"])
        return []

    monkeypatch.setattr("pd_runner.services.bot_profile.run_cells", fake_run_cells)
    build_profile("WaryBot", opponents=("CooperateBot",), budgets=(2,),
                  jobs=16, memory_mb=2048)

    assert seen["jobs"] * seen["memory_mb"] <= MAX_TOTAL_MEMORY_MB
    assert seen["jobs"] >= 1, "clamping must never reach zero workers"


def test_clamp_leaves_a_modest_request_alone(monkeypatch: pytest.MonkeyPatch) -> None:
    seen: dict[str, int] = {}
    monkeypatch.setattr(
        "pd_runner.services.bot_profile.run_cells",
        lambda cells, **kw: (seen.update(jobs=kw["jobs"]), [])[1],
    )
    build_profile("WaryBot", opponents=("CooperateBot",), budgets=(2,),
                  jobs=2, memory_mb=2048)
    assert seen["jobs"] == 2


def test_default_footprint_is_within_the_ceiling() -> None:
    assert DEFAULT_JOBS * PROFILE_MEMORY_MB <= MAX_TOTAL_MEMORY_MB


def test_memory_cap_stays_above_the_measured_floor() -> None:
    """MEASURED: WaryBot vs CooperateBot at k=2 is determined at 3072MB and
    dies with a memory_exception at 2560MB. Lowering the cap does not make the
    sweep safer — it silently converts determined cells into `undetermined`,
    which reads exactly like a genuine Löb boundary. Cut `jobs` instead."""
    assert PROFILE_MEMORY_MB >= 3072


def test_behavior_key_ignores_timing_but_tracks_behavior() -> None:
    """The rewriter's stop-early guard compares profiles across attempts. It must
    NOT use `==`: `raw` carries per-cell wall-clock seconds, so behaviorally
    identical runs compare unequal and the guard would never fire."""
    def prof(outcome: str, seconds: float) -> BotProfile:
        r = [_cell("CooperateBot", 2, "determined", outcome)]
        r[0].seconds = seconds
        return BotProfile("B", (_classify("CooperateBot", r),), (2,), raw=tuple(r))

    same_a, same_b, changed = prof("(C, C)", 1.0), prof("(C, C)", 9.9), prof("(D, D)", 1.0)

    assert same_a != same_b, "precondition: == is timing-sensitive"
    assert same_a.behavior_key() == same_b.behavior_key(), "timing must not register"
    assert same_a.behavior_key() != changed.behavior_key(), "real change must register"


def test_build_profile_rejects_unregistered_bot_without_source() -> None:
    with pytest.raises(ValueError, match="not in the prepass registry"):
        build_profile("TotallyNewBot")


def test_build_profile_rejects_unknown_opponent() -> None:
    with pytest.raises(ValueError, match="unknown opponent"):
        build_profile("WaryBot", opponents=("NoSuchOpponent",))


def test_default_budgets_span_the_known_transition() -> None:
    """WaryBot's (C,D)→(D,D) transition sits between 4 and 16; the sweep must
    include points on both sides or the transition is invisible."""
    assert min(DEFAULT_BUDGETS) <= 4
    assert max(DEFAULT_BUDGETS) >= 16


# ---------------------------------------------------------------------------
# staged_bot — filesystem only, no Lean invocation
# ---------------------------------------------------------------------------


def _llm_dir(engine: Path) -> Path:
    return engine / "PrisonersDilemma" / "Bots" / "LlmGenerations"


def test_staged_bot_writes_then_removes(tmp_path: Path) -> None:
    target = _llm_dir(tmp_path) / "TempBot.lean"
    with staged_bot("TempBot", "def TempBot : Prog := x", engine_dir=tmp_path) as module:
        assert module == "PrisonersDilemma.Bots.LlmGenerations.TempBot"
        assert target.read_text().endswith("\n")
        assert "def TempBot" in target.read_text()
    assert not target.exists(), "staged source must not survive the context"


def test_staged_bot_removes_source_even_on_error(tmp_path: Path) -> None:
    target = _llm_dir(tmp_path) / "TempBot.lean"
    with pytest.raises(RuntimeError):
        with staged_bot("TempBot", "def TempBot : Prog := x", engine_dir=tmp_path):
            assert target.exists()
            raise RuntimeError("boom")
    assert not target.exists()


def test_staged_bot_refuses_to_clobber_an_existing_bot(tmp_path: Path) -> None:
    """An accepted library bot must never be overwritten — and, worse, deleted
    on context exit — by a profiling run."""
    target = _llm_dir(tmp_path) / "RealBot.lean"
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("-- the real, accepted bot\n", encoding="utf-8")

    with pytest.raises(FileExistsError, match="already exists"):
        with staged_bot("RealBot", "def RealBot : Prog := impostor", engine_dir=tmp_path):
            pass

    assert target.read_text() == "-- the real, accepted bot\n", "existing bot was modified"


def test_staged_bot_cleans_build_artifacts(tmp_path: Path) -> None:
    """A stale .olean would let a later import silently succeed against code
    whose source no longer exists."""
    lib = tmp_path / ".lake" / "build" / "lib" / "lean" / "PrisonersDilemma" / "Bots" / "LlmGenerations"
    ir = tmp_path / ".lake" / "build" / "ir" / "PrisonersDilemma" / "Bots" / "LlmGenerations"
    for d in (lib, ir):
        d.mkdir(parents=True, exist_ok=True)

    keep = lib / "OtherBot.olean"
    keep.write_text("keep me")

    with staged_bot("TempBot", "def TempBot : Prog := x", engine_dir=tmp_path):
        for artifact in (
            lib / "TempBot.olean", lib / "TempBot.olean.hash", lib / "TempBot.trace",
            ir / "TempBot.c", ir / "TempBot.setup.json",
        ):
            artifact.write_text("stale")

    assert not list(lib.glob("TempBot.*")), "lib artifacts survived"
    assert not list(ir.glob("TempBot.*")), "ir artifacts survived"
    assert keep.exists(), "unrelated bot's artifacts were deleted"

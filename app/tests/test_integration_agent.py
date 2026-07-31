"""Unit tests for the integration agent's episode/verdict machinery
(services/constructor_integration.py) — the tool-level gate only; the full
worktree flow needs a live repo + lake and is exercised via the API."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

from pd_runner.llm.client import EpisodeStop
from pd_runner.services import constructor_integration as ci


def _handler_with_builds(monkeypatch, tmp_path: Path, build_results):
    """A tool handler whose lake builds pop from `build_results` (returncode ints)."""
    seq = list(build_results)

    def fake_build(engine_dir, target=None):
        code = seq.pop(0)
        return SimpleNamespace(returncode=code, stdout=f"build {target}", stderr="" if code == 0 else "error: boom")

    monkeypatch.setattr(ci, "build_lean_project", fake_build)
    state = ci._IntegrationState()
    _, handler = ci._make_tools(tmp_path, state)
    return handler, state


def test_complete_verdict_accepted_when_both_targets_green(monkeypatch, tmp_path):
    handler, _ = _handler_with_builds(monkeypatch, tmp_path, [0, 0])
    outcome = handler.call(
        "submit_integration_result", {"verdict": "complete", "summary": "did the thing"}
    )
    assert isinstance(outcome, EpisodeStop)
    assert outcome.payload["verdict"] == "complete"


def test_complete_verdict_bounces_on_failing_build(monkeypatch, tmp_path):
    # First verification: engine green, metatheory fails → rejection string.
    # Second attempt: both green → accepted.
    handler, state = _handler_with_builds(monkeypatch, tmp_path, [0, 1, 0, 0])
    rejection = handler.call(
        "submit_integration_result", {"verdict": "complete", "summary": "s"}
    )
    assert isinstance(rejection, str) and "Result rejected" in rejection
    assert "Metatheory" in rejection
    assert state.build_bounces == 1
    accepted = handler.call(
        "submit_integration_result", {"verdict": "complete", "summary": "s"}
    )
    assert isinstance(accepted, EpisodeStop)


def test_complete_verdict_bounce_cap_ends_episode(monkeypatch, tmp_path):
    handler, state = _handler_with_builds(monkeypatch, tmp_path, [1, 1, 1, 1, 1, 1])
    for _ in range(3):
        out = handler.call(
            "submit_integration_result", {"verdict": "complete", "summary": "s"}
        )
        assert isinstance(out, str)
    capped = handler.call(
        "submit_integration_result", {"verdict": "complete", "summary": "s"}
    )
    assert isinstance(capped, EpisodeStop)
    assert capped.payload is None
    assert capped.end_reason == "verification_cap"


def test_blocked_verdict_needs_no_build(monkeypatch, tmp_path):
    handler, _ = _handler_with_builds(monkeypatch, tmp_path, [])  # any build call would pop from empty
    outcome = handler.call(
        "submit_integration_result",
        {"verdict": "blocked", "summary": "T49 substrate arm irreparable: <error>"},
    )
    assert isinstance(outcome, EpisodeStop)
    assert outcome.payload["verdict"] == "blocked"


def test_verdict_requires_summary(monkeypatch, tmp_path):
    handler, _ = _handler_with_builds(monkeypatch, tmp_path, [])
    out = handler.call("submit_integration_result", {"verdict": "complete", "summary": ""})
    assert isinstance(out, str) and "summary" in out


def test_notebook_tool_records_state(monkeypatch, tmp_path):
    handler, state = _handler_with_builds(monkeypatch, tmp_path, [])
    out = handler.call("update_notebook", {"notebook": "step 1 done; Pf.induct arm pending"})
    assert "Notebook updated" in out
    assert state.notebook == "step 1 done; Pf.induct arm pending"


def test_lake_build_records_last_output(monkeypatch, tmp_path):
    handler, state = _handler_with_builds(monkeypatch, tmp_path, [1])
    out = handler.call("run_lake_build", {"target": "PrisonersDilemma"})
    assert "exit_code: 1" in out
    assert "PrisonersDilemma" in state.last_build_output

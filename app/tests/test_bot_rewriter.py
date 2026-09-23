"""Rewriter loop tests — termination, selection, and the invariants.

No LLM and no Lean: `search_bot` and `evaluate_against` are stubbed, so these
test the loop's control flow, which is where the bugs live. The invariants under
test are the ones from docs/BOT_REVIEWER.md §7:

  * the expectation is extracted exactly ONCE per run;
  * a rewrite fires only on strong evidence;
  * the loop terminates on the budget, on unchanged behavior, and on a writer
    failure;
  * the best attempt wins, ties going to the earlier one.
"""

from __future__ import annotations

import pytest

from pd_runner.eval.outcome_prepass import CellResult
from pd_runner.services import bot_rewriter as mod
from pd_runner.services.bot_expectation import Expectation, ExpectedCell, compare
from pd_runner.services.bot_profile import BotProfile, _classify
from pd_runner.services.bot_service import BotResult, BotWriteError


def _profile(bot: str, cells: dict[str, str]) -> BotProfile:
    built = [
        _classify(opp, [CellResult(bot, opp, 2, 2, 64, "determined", out, "n", 1.0)])
        for opp, out in cells.items()
    ]
    return BotProfile(bot_name=bot, cells=tuple(built), budgets=(2,))


_EXPECTATION = Expectation(
    cells=(
        ExpectedCell("CooperateBot", "C", "explicit", "stated"),
        ExpectedCell("DefectBot", "D", "explicit", "stated"),
    ),
    summary="nice but retaliatory",
)

_BAD = {"CooperateBot": "(C, C)", "DefectBot": "(C, D)"}    # DefectBot wrong
_GOOD = {"CooperateBot": "(C, C)", "DefectBot": "(D, D)"}   # both right
_WORSE = {"CooperateBot": "(D, C)", "DefectBot": "(C, D)"}  # both wrong


@pytest.fixture
def harness(monkeypatch):
    """Stub the LLM and Lean layers; record what the loop did."""
    calls = {"extract": 0, "search": 0, "feedback": []}

    def fake_extract(*a, **kw):
        calls["extract"] += 1
        return _EXPECTATION

    def fake_evaluate(bot_name, lean_source, expectation, **kw):
        profile = _profile(bot_name, state["profiles"].pop(0))
        return profile, compare(expectation, profile)

    def fake_search_bot(request):
        calls["search"] += 1
        calls["feedback"].append(request.feedback)
        if state.get("writer_raises"):
            raise BotWriteError("no compiling bot")
        return BotResult(request.bot_name, f"-- source v{calls['search']}", 1)

    state: dict = {"profiles": []}
    monkeypatch.setattr(mod, "extract_expectation", fake_extract)
    monkeypatch.setattr(mod, "evaluate_against", fake_evaluate)
    monkeypatch.setattr(mod, "search_bot", fake_search_bot)
    monkeypatch.setattr(mod, "persist_review", lambda *a, **kw: None)
    return calls, state


def _run(state, profiles, **kw):
    state["profiles"] = list(profiles)
    return mod.rewrite_until_faithful(
        "B", "nice but retaliatory", BotResult("B", "-- initial", 1), **kw
    )


def test_faithful_first_attempt_never_rewrites(harness) -> None:
    calls, state = harness
    run = _run(state, [_GOOD])

    assert run.stop_reason == "faithful"
    assert len(run.attempts) == 1
    assert calls["search"] == 0, "a faithful bot must not be rewritten"
    assert run.best.index == 0


def test_rewrite_fixes_the_bot_and_stops(harness) -> None:
    calls, state = harness
    run = _run(state, [_BAD, _GOOD])

    assert run.stop_reason == "faithful"
    assert len(run.attempts) == 2
    assert calls["search"] == 1
    assert run.best.index == 1 and run.best.hard_failures == 0
    assert run.improved


def test_expectation_is_extracted_exactly_once(harness) -> None:
    """The invariant that keeps the review independent across attempts."""
    calls, state = harness
    _run(state, [_BAD, _WORSE, _BAD])
    assert calls["extract"] == 1


def test_feedback_carries_the_mismatch_brief(harness) -> None:
    calls, state = harness
    _run(state, [_BAD, _GOOD])

    brief = calls["feedback"][0]
    assert brief is not None
    assert "DefectBot" in brief
    assert "CooperateBot" not in brief, "passing cells must not leak to the writer"


def test_budget_is_respected(harness) -> None:
    calls, state = harness
    run = _run(state, [_BAD, _WORSE, _BAD, _WORSE], max_rewrites=2)

    assert run.stop_reason == "max_attempts"
    assert calls["search"] == 2, "at most max_rewrites writer calls"
    assert len(run.attempts) == 3, "initial + 2 rewrites"


def test_unchanged_behavior_stops_early(harness) -> None:
    """Same behavior twice = the writer did not act on the feedback; a third
    identical attempt would only burn budget."""
    calls, state = harness
    run = _run(state, [_BAD, _BAD, _GOOD], max_rewrites=2)

    assert run.stop_reason == "no_behavior_change"
    assert calls["search"] == 1, "must not spend the second rewrite"
    assert len(run.attempts) == 2


def test_writer_failure_ends_the_run_with_the_best_so_far(harness) -> None:
    calls, state = harness
    state["writer_raises"] = True
    run = _run(state, [_BAD])

    assert run.stop_reason == "writer_failed"
    assert len(run.attempts) == 1
    assert run.best.index == 0


def test_best_attempt_minimises_hard_failures(harness) -> None:
    calls, state = harness
    run = _run(state, [_BAD, _WORSE, _GOOD], max_rewrites=2)

    assert run.best.index == 2
    assert run.best.hard_failures == 0


def test_ties_go_to_the_earlier_attempt(harness) -> None:
    """A rewrite must EARN its place: the initial bot was written against the
    full description, a rewrite only against a mismatch list."""
    calls, state = harness
    # Two different behaviors, equal hard-failure counts (1 each).
    run = _run(state, [_BAD, {"CooperateBot": "(D, C)", "DefectBot": "(D, D)"}],
               max_rewrites=1)

    assert run.attempts[0].hard_failures == run.attempts[1].hard_failures == 1
    assert run.best.index == 0


def test_oscillation_is_detected(harness) -> None:
    calls, state = harness
    run = _run(state, [_BAD, _WORSE, _BAD], max_rewrites=2)

    assert run.oscillated, "returning to an earlier behavior must be flagged"
    assert "ambiguous" in run.render()


def test_no_oscillation_on_monotone_progress(harness) -> None:
    calls, state = harness
    run = _run(state, [_WORSE, _BAD, _GOOD], max_rewrites=2)
    assert not run.oscillated


def test_render_marks_the_selected_attempt(harness) -> None:
    calls, state = harness
    run = _run(state, [_BAD, _GOOD])
    assert "selected" in run.render()
    assert run.render().count("attempt") >= 2

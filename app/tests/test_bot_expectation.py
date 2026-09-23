"""Tier A1 tests — the blind extractor and the deterministic comparison.

No LLM calls: the extractor is exercised through a stubbed client, and
`compare()` is pure logic. The properties under test are the ones that decide
whether the reviewer is trustworthy enough to gate on:

  * `unspecified` never counts as a failure (else partial descriptions, which
    are the common case, produce constant false alarms);
  * `inferred` mismatches warn, `explicit` mismatches fail (else the
    false-positive rate is set by how freely the extractor extrapolates);
  * a budget phase transition is never a mismatch (else a budget artifact reads
    as a faithfulness failure — the WaryBot-vs-DefectBot trap).
"""

from __future__ import annotations

import pytest

from pd_runner.eval.outcome_prepass import CellResult
from pd_runner.services.bot_expectation import (
    ExpectedCell,
    Expectation,
    compare,
)
from pd_runner.services.bot_profile import BotProfile, _classify


def _profile(bot: str, cells: dict[str, list[tuple[int, str | None]]]) -> BotProfile:
    """Build a profile from {opponent: [(budget, "(C, D)" or None), ...]}."""
    built = []
    for opp, ladder in cells.items():
        results = [
            CellResult(
                left=bot, right=opp, budget=k, fuel_d=k, fuel=64,
                status="determined" if out else "undetermined",
                outcome=out, note="" if out else "Löb boundary", seconds=1.0,
            )
            for k, out in ladder
        ]
        built.append(_classify(opp, results))
    return BotProfile(bot_name=bot, cells=tuple(built), budgets=(2,))


def _expect(**kw: tuple[str, str]) -> Expectation:
    """_expect(DefectBot=("D", "explicit"), ...)"""
    return Expectation(
        cells=tuple(
            ExpectedCell(opponent=o, my_action=a, confidence=c, rationale="because")
            for o, (a, c) in kw.items()
        )
    )


def test_all_cells_match_is_faithful() -> None:
    exp = _expect(CooperateBot=("C", "explicit"), DefectBot=("D", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert r.verdict == "faithful"
    assert not r.hard_failures
    assert len(r.checked) == 2


def test_explicit_mismatch_is_a_hard_failure() -> None:
    exp = _expect(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)")]})
    r = compare(exp, prof)
    assert r.verdict == "mismatch"
    assert len(r.hard_failures) == 1
    assert r.cells[0].expected == "D" and r.cells[0].actual == "C"


def test_inferred_mismatch_warns_but_does_not_fail() -> None:
    """The extractor extrapolated; that is not strong enough to reject a bot."""
    exp = _expect(MirrorBot=("C", "inferred"))
    prof = _profile("B", {"MirrorBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert r.cells[0].kind == "mismatch"
    assert not r.cells[0].is_hard_failure
    assert len(r.warnings) == 1
    assert r.verdict == "faithful"


def test_unanimous_inferred_mismatch_is_a_failure() -> None:
    """Regression: an inverted-polarity GuardianBot produced FOUR inferred
    mismatches and still scored `faithful`, because each one alone is only a
    warning. Unanimity across certified cells is not weak evidence."""
    exp = _expect(
        CooperateBot=("D", "inferred"), DefectBot=("C", "inferred"),
        MirrorBot=("D", "inferred"), TitForTatBot=("D", "inferred"),
    )
    prof = _profile("B", {
        "CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")],
        "MirrorBot": [(2, "(C, C)")], "TitForTatBot": [(2, "(C, C)")],
    })
    r = compare(exp, prof)
    assert r.unanimous_mismatch
    assert r.verdict == "mismatch"
    assert not r.hard_failures, "these are inferred, not explicit"


def test_one_lone_inferred_mismatch_still_only_warns() -> None:
    """The confidence split must survive: a single extrapolation that misses is
    exactly the weak evidence it exists to discount."""
    exp = _expect(MirrorBot=("C", "inferred"))
    prof = _profile("B", {"MirrorBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert not r.unanimous_mismatch
    assert r.verdict == "faithful"


def test_partial_inferred_mismatch_does_not_trigger_unanimity() -> None:
    exp = _expect(CooperateBot=("C", "inferred"), DefectBot=("C", "inferred"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert not r.unanimous_mismatch
    assert r.verdict == "faithful"


def test_unspecified_is_never_a_failure() -> None:
    exp = _expect(TitForTatBot=("unspecified", "inferred"))
    prof = _profile("B", {"TitForTatBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert r.cells[0].kind == "unspecified"
    assert not r.hard_failures
    assert r.needs_judge


def test_phase_dependent_cell_is_not_a_mismatch() -> None:
    """WaryBot vs DefectBot: (C,D) low-k, (D,D) high-k. A description saying
    'defects against defectors' must NOT be failed on the low-k sample."""
    exp = _expect(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)"), (16, "(D, D)")]})
    r = compare(exp, prof)
    assert r.cells[0].kind == "uncertified"
    assert not r.hard_failures
    assert r.verdict != "mismatch"
    assert r.needs_judge
    assert "budget-dependent" in r.cells[0].detail


def test_uncertified_cell_defers_rather_than_failing() -> None:
    exp = _expect(MirrorBot=("C", "explicit"))
    prof = _profile("B", {"MirrorBot": [(2, None)]})
    r = compare(exp, prof)
    assert r.cells[0].kind == "uncertified"
    assert not r.hard_failures
    assert any("MirrorBot" in u for u in r.unresolved)


def test_no_certified_cells_is_underdetermined_not_faithful() -> None:
    """Zero evidence must not read as a pass."""
    exp = _expect(MirrorBot=("C", "explicit"))
    prof = _profile("B", {"MirrorBot": [(2, None)]})
    assert compare(exp, prof).verdict == "underdetermined"


def test_structural_claims_go_to_the_judge() -> None:
    exp = Expectation(
        cells=(ExpectedCell("CooperateBot", "C", "explicit", "stated"),),
        structural_claims=("punishes via a third-party probe",),
    )
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    r = compare(exp, prof)
    assert r.verdict == "faithful"
    assert r.needs_judge
    assert "third-party probe" in r.unresolved[0]


def test_missing_profile_cell_is_uncertified() -> None:
    exp = _expect(DefectBot=("D", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    r = compare(exp, prof)
    assert r.cells[0].kind == "uncertified"
    assert not r.hard_failures


def test_mixed_profile_reports_every_category() -> None:
    exp = _expect(
        CooperateBot=("C", "explicit"),
        DefectBot=("C", "explicit"),
        MirrorBot=("unspecified", "inferred"),
        TitForTatBot=("C", "explicit"),
    )
    prof = _profile("B", {
        "CooperateBot": [(2, "(C, C)")],
        "DefectBot": [(2, "(D, D)")],
        "MirrorBot": [(2, "(C, C)")],
        "TitForTatBot": [(2, None)],
    })
    r = compare(exp, prof)
    kinds = {c.opponent: c.kind for c in r.cells}
    assert kinds == {
        "CooperateBot": "match",
        "DefectBot": "mismatch",
        "MirrorBot": "unspecified",
        "TitForTatBot": "uncertified",
    }
    assert r.verdict == "mismatch"
    assert "MISMATCH" in r.render()


# ---------------------------------------------------------------------------
# Rewriter prerequisites (docs/BOT_REVIEWER.md §7)
# ---------------------------------------------------------------------------


def test_should_rewrite_fires_on_explicit_mismatch() -> None:
    exp = _expect(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)")]})
    assert compare(exp, prof).should_rewrite


def test_should_rewrite_fires_on_unanimous_mismatch() -> None:
    exp = _expect(CooperateBot=("D", "inferred"), DefectBot=("C", "inferred"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")]})
    r = compare(exp, prof)
    assert not r.hard_failures and r.should_rewrite


def test_should_rewrite_does_not_fire_on_weak_evidence() -> None:
    """The whole point of the predicate: never rewrite on a lone inferred
    mismatch, an unspecified cell, or an uncertified cell."""
    lone_inferred = compare(
        _expect(MirrorBot=("C", "inferred")),
        _profile("B", {"MirrorBot": [(2, "(D, D)")]}),
    )
    unspecified = compare(
        _expect(MirrorBot=("unspecified", "inferred")),
        _profile("B", {"MirrorBot": [(2, "(D, D)")]}),
    )
    uncertified = compare(
        _expect(MirrorBot=("C", "explicit")),
        _profile("B", {"MirrorBot": [(2, None)]}),
    )
    assert not lone_inferred.should_rewrite
    assert not unspecified.should_rewrite
    assert not uncertified.should_rewrite


def test_mismatch_brief_reports_failures_not_the_answer_key() -> None:
    """The brief must name the failing cells only — never the passing ones, or
    the writer fits the canonical opponents instead of the strategy."""
    exp = _expect(
        CooperateBot=("C", "explicit"),   # passes
        DefectBot=("D", "explicit"),      # fails
    )
    prof = _profile("B", {
        "CooperateBot": [(2, "(C, C)")],
        "DefectBot": [(2, "(C, D)")],
    })
    brief = compare(exp, prof).mismatch_brief()

    assert "DefectBot" in brief
    assert "CooperateBot" not in brief, "passing cells must not leak into the brief"
    assert "D" in brief and "C" in brief


def test_mismatch_brief_flags_inverted_core_logic() -> None:
    exp = _expect(CooperateBot=("D", "inferred"), DefectBot=("C", "inferred"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")]})
    assert "inverted" in compare(exp, prof).mismatch_brief()


def test_evaluate_against_takes_an_injected_expectation() -> None:
    """Signature guarantee: the expectation is passed IN, so the rewriter cannot
    accidentally re-extract per attempt and let the prediction drift."""
    import inspect

    from pd_runner.services.bot_expectation import evaluate_against

    params = inspect.signature(evaluate_against).parameters
    assert "expectation" in params
    assert "strategy_description" not in params, (
        "evaluate_against must not be able to extract its own expectation"
    )


def test_persist_review_writes_one_row_per_attempt(tmp_path, monkeypatch) -> None:
    import json as _json

    from pd_runner.config import AppPaths
    from pd_runner.services import bot_expectation as mod

    monkeypatch.setattr(
        "pd_runner.config.load_paths",
        lambda: AppPaths(tmp_path, tmp_path, tmp_path, tmp_path),
    )

    exp = _expect(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)")]})
    cmp_ = compare(exp, prof)

    p1 = mod.persist_review("B", "desc", "src v1", exp, prof, cmp_, attempt=0, run_ts="T")
    p2 = mod.persist_review("B", "desc", "src v2", exp, prof, cmp_, attempt=1, run_ts="T")

    assert p1 == p2, "attempts of one run share a file"
    rows = [_json.loads(line) for line in p1.read_text().splitlines() if line.strip()]
    assert [r["attempt"] for r in rows] == [0, 1]
    assert [r["lean_source"] for r in rows] == ["src v1", "src v2"]
    assert rows[0]["should_rewrite"] is True
    assert rows[0]["behavior_key"] == [["DefectBot", "stable", "C"]]


def test_bot_request_message_omits_retry_block_on_first_attempt() -> None:
    from pd_runner.llm.prompts import bot_request_message

    msg = bot_request_message("MyBot", "always cooperate")
    assert "REWRITE" not in msg
    assert "always cooperate" in msg


def test_bot_request_message_carries_feedback_on_rewrite() -> None:
    from pd_runner.llm.prompts import bot_request_message

    msg = bot_request_message(
        "MyBot", "punish bullies",
        feedback="- Against DefectBot: the description implies D, but it plays C.",
    )
    assert "REWRITE" in msg
    assert "Against DefectBot" in msg
    assert "punish bullies" in msg, "the specification must still be present"
    # The writer must be told to fix the logic, not special-case the opponent.
    assert "special-case" in msg


def test_bot_request_feedback_flows_through_to_the_prompt(monkeypatch) -> None:
    """End-to-end plumbing: BotRequest.feedback -> the user turn the writer sees."""
    from pd_runner.services import bot_service

    seen: dict[str, str] = {}

    class FakeClient:
        last_tool_calls = 1

        def __init__(self, *a, **kw) -> None: ...
        def run(self, user_message, tool_handler=None):
            seen["msg"] = user_message
            return "```lean\ndef MyBot : Prog := .const Action.C\n```"

    monkeypatch.setattr(bot_service, "make_llm_client", lambda *a, **kw: FakeClient())
    monkeypatch.setattr(bot_service, "build_bot_system_prompt", lambda: "sys")

    bot_service.search_bot(bot_service.BotRequest(
        bot_name="MyBot", strategy_description="punish bullies",
        feedback="- Against DefectBot: implies D, plays C.",
    ))
    assert "REWRITE" in seen["msg"]
    assert "Against DefectBot" in seen["msg"]


def test_extractor_is_blind_by_signature() -> None:
    """Structural guarantee: the extractor takes a description, never a bot
    result or Lean source. If this ever grows a `lean_source` parameter the
    whole comparison stops being independent evidence."""
    import inspect

    from pd_runner.services.bot_expectation import extract_expectation

    params = inspect.signature(extract_expectation).parameters
    assert "strategy_description" in params
    for leaky in ("lean_source", "bot_result", "source", "profile", "bot"):
        assert leaky not in params, f"extractor must not receive {leaky!r}"


def test_extractor_parses_a_submission(monkeypatch: pytest.MonkeyPatch) -> None:
    """Stubbed client: check payload -> Expectation, including the default for
    an opponent the model silently omitted."""
    from pd_runner.llm.client import EpisodeResult, UsageTotals
    from pd_runner.services import bot_expectation as mod

    payload = {
        "cells": [
            {"opponent": "CooperateBot", "my_action": "C",
             "confidence": "explicit", "rationale": "stated"},
            {"opponent": "DefectBot", "my_action": "D",
             "confidence": "inferred", "rationale": "extrapolated"},
        ],
        "structural_claims": ["third-party probe"],
        "summary": "nice but retaliatory",
    }

    class FakeClient:
        def __init__(self, *a, **kw) -> None: ...
        def run_episode(self, *a, **kw):
            return EpisodeResult(
                verdict_input=payload, end_reason="expectation", turns_used=1,
                tool_calls_used=1, usage=UsageTotals(), final_text="", messages=[],
            )

    monkeypatch.setattr(mod, "make_llm_client", lambda *a, **kw: FakeClient())
    exp = mod.extract_expectation("nice but retaliatory")

    assert exp.cell("CooperateBot").my_action == "C"
    assert exp.cell("DefectBot").confidence == "inferred"
    # Omitted opponents default to unspecified — never to a guess.
    assert exp.cell("MirrorBot").my_action == "unspecified"
    assert exp.cell("TitForTatBot").my_action == "unspecified"
    assert exp.structural_claims == ("third-party probe",)
    assert len(exp.specified_cells) == 2


def test_extractor_raises_when_no_prediction_submitted(monkeypatch: pytest.MonkeyPatch) -> None:
    from pd_runner.llm.client import EpisodeResult, UsageTotals
    from pd_runner.services import bot_expectation as mod

    class FakeClient:
        def __init__(self, *a, **kw) -> None: ...
        def run_episode(self, *a, **kw):
            return EpisodeResult(
                verdict_input=None, end_reason="turn_cap", turns_used=4,
                tool_calls_used=0, usage=UsageTotals(), final_text="", messages=[],
            )

    monkeypatch.setattr(mod, "make_llm_client", lambda *a, **kw: FakeClient())
    with pytest.raises(RuntimeError, match="did not submit"):
        mod.extract_expectation("whatever")

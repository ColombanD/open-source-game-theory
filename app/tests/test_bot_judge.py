"""Tier B tests — the judge's scoping and parsing, no LLM calls.

The property that matters most is SCOPE: the judge must be asked only about what
Tier A could not decide. Certified cells are machine proofs; inviting a judge to
second-guess them is how an opinion starts overturning a theorem.
"""

from __future__ import annotations

import pytest

from pd_runner.eval.outcome_prepass import CellResult
from pd_runner.services.bot_expectation import (
    Expectation,
    ExpectedCell,
    compare,
)
from pd_runner.services.bot_judge import JudgeReview, _residual_brief, judge_residual
from pd_runner.services.bot_profile import BotProfile, _classify


def _profile(bot: str, cells: dict[str, list[tuple[int, str | None]]]) -> BotProfile:
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


def _expectation(**kw: tuple[str, str]) -> Expectation:
    return Expectation(
        cells=tuple(
            ExpectedCell(opponent=o, my_action=a, confidence=c, rationale="stated")
            for o, (a, c) in kw.items()
        )
    )


def _brief(expectation: Expectation, profile: BotProfile, source: str = "def B := x") -> str:
    return _residual_brief(
        "B", "some strategy", source, expectation, profile, compare(expectation, profile)
    )


def test_certified_cells_are_marked_settled_not_asked() -> None:
    """A machine-proved cell goes in as context, never as an open question."""
    exp = _expectation(CooperateBot=("C", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    brief = _brief(exp, prof)

    settled, open_section = brief.split("## OPEN questions")
    assert "CooperateBot" in settled
    assert "CERTIFIED" in settled
    assert "CooperateBot" not in open_section


def test_established_mismatch_is_settled_not_reopened() -> None:
    """The judge must not be invited to argue away a certified mismatch."""
    exp = _expectation(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)")]})
    brief = _brief(exp, prof)

    settled, open_section = brief.split("## OPEN questions")
    assert "MISMATCH already established" in settled
    assert "DefectBot" not in open_section


def test_uncertified_cell_becomes_an_open_question_with_its_ladder() -> None:
    exp = _expectation(MirrorBot=("C", "explicit"))
    prof = _profile("B", {"MirrorBot": [(2, None), (16, None)]})
    open_section = _brief(exp, prof).split("## OPEN questions")[1]

    assert "MirrorBot" in open_section
    assert "k=2" in open_section and "k=16" in open_section


def test_phase_dependent_cell_reaches_the_judge_with_the_full_ladder() -> None:
    """The WaryBot shape: the judge needs every rung to rule on the ladder."""
    exp = _expectation(DefectBot=("D", "explicit"))
    prof = _profile("B", {"DefectBot": [(2, "(C, D)"), (16, "(D, D)")]})
    open_section = _brief(exp, prof).split("## OPEN questions")[1]

    assert "DefectBot" in open_section
    assert "k=2: (C, D)" in open_section
    assert "k=16: (D, D)" in open_section


def test_unspecified_cell_is_asked_as_a_consistency_question() -> None:
    exp = _expectation(TitForTatBot=("unspecified", "inferred"))
    prof = _profile("B", {"TitForTatBot": [(2, "(D, D)")]})
    open_section = _brief(exp, prof).split("## OPEN questions")[1]

    assert "does not settle this cell" in open_section
    assert "consistent" in open_section


def test_structural_claims_reach_the_judge() -> None:
    exp = Expectation(
        cells=(ExpectedCell("CooperateBot", "C", "explicit", "stated"),),
        structural_claims=("punishes via a frozen third-party probe",),
    )
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    open_section = _brief(exp, prof).split("## OPEN questions")[1]

    assert "third-party probe" in open_section


def test_brief_embeds_the_source_and_description() -> None:
    exp = _expectation(CooperateBot=("C", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    brief = _brief(exp, prof, source="def B (k : Nat) : Prog := .search k g a b")

    assert ".search k g a b" in brief
    assert "some strategy" in brief


def test_fully_certified_review_has_no_open_questions() -> None:
    exp = _expectation(CooperateBot=("C", "explicit"), DefectBot=("D", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")], "DefectBot": [(2, "(D, D)")]})
    open_section = _brief(exp, prof).split("## OPEN questions")[1]

    assert "(none)" in open_section


# ---------------------------------------------------------------------------
# Verdict parsing
# ---------------------------------------------------------------------------


def _fake_client(payload, monkeypatch) -> None:
    from pd_runner.llm.client import EpisodeResult, UsageTotals
    from pd_runner.services import bot_judge as mod

    class FakeClient:
        def __init__(self, *a, **kw) -> None: ...
        def run_episode(self, *a, **kw):
            return EpisodeResult(
                verdict_input=payload, end_reason="review", turns_used=1,
                tool_calls_used=1, usage=UsageTotals(), final_text="", messages=[],
            )

    monkeypatch.setattr(mod, "make_llm_client", lambda *a, **kw: FakeClient())


def _run_judge() -> JudgeReview:
    exp = _expectation(CooperateBot=("C", "explicit"))
    prof = _profile("B", {"CooperateBot": [(2, "(C, C)")]})
    return judge_residual("B", "desc", "def B := x", exp, prof, compare(exp, prof))


def test_parses_a_mismatch_with_discrepancies(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_client({
        "kind": "mismatch",
        "discrepancies": [{
            "claim": "punishes bullies",
            "expected": "D against a bully",
            "actual": "cooperates unconditionally",
            "severity": "blocking",
            "evidence": ".const Action.C",
        }],
        "notes": "the guard is never consulted",
    }, monkeypatch)

    r = _run_judge()
    assert r.kind == "mismatch"
    assert len(r.blocking) == 1
    assert r.blocking[0].evidence == ".const Action.C"
    assert "blocking" in r.render()


def test_non_blocking_discrepancies_are_not_blocking(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_client({
        "kind": "faithful",
        "discrepancies": [
            {"claim": "c", "expected": "e", "actual": "a", "severity": "note", "evidence": "x"},
            {"claim": "c", "expected": "e", "actual": "a", "severity": "concern", "evidence": "y"},
        ],
    }, monkeypatch)

    r = _run_judge()
    assert r.kind == "faithful"
    assert r.blocking == ()
    assert len(r.discrepancies) == 2


def test_missing_review_degrades_to_underdetermined(monkeypatch: pytest.MonkeyPatch) -> None:
    """A judge that fails must not silently read as approval."""
    from pd_runner.llm.client import EpisodeResult, UsageTotals
    from pd_runner.services import bot_judge as mod

    class FakeClient:
        def __init__(self, *a, **kw) -> None: ...
        def run_episode(self, *a, **kw):
            return EpisodeResult(
                verdict_input=None, end_reason="turn_cap", turns_used=8,
                tool_calls_used=0, usage=UsageTotals(), final_text="", messages=[],
            )

    monkeypatch.setattr(mod, "make_llm_client", lambda *a, **kw: FakeClient())

    r = _run_judge()
    assert r.kind == "underdetermined"
    assert r.unresolved and "turn_cap" in r.unresolved[0]


def test_unknown_kind_defaults_to_underdetermined(monkeypatch: pytest.MonkeyPatch) -> None:
    _fake_client({"discrepancies": [], "notes": "no kind field"}, monkeypatch)
    assert _run_judge().kind == "underdetermined"

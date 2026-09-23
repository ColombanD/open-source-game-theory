"""API surface for the faithfulness review + rewriter.

Guards the contract between the reviewer services and the web app: the request
knobs exist, a review survives serialisation into `JobResponse`, and the UI
actually ships the rendering code. Without these, the reviewer can keep working
while silently disappearing from the app.
"""

from __future__ import annotations

from fastapi.testclient import TestClient

from pd_runner.api.jobs import Job
from pd_runner.api.main import app
from pd_runner.api.schemas import JobStatus, PipelineRequest
from pd_runner.services.bot_service import BotResult

_REVIEW = {
    "verdict": "mismatch",
    "summary": "nice but retaliatory",
    "cells": [
        {"opponent": "DefectBot", "kind": "mismatch", "expected": "D",
         "expected_confidence": "explicit", "actual": "C",
         "detail": "expected D, engine certifies C"},
    ],
    "hard_failures": 1,
    "warnings": 0,
    "unanimous_mismatch": False,
    "coverage": "4/4 opponents certified",
    "profile_lines": ["vs DefectBot: C (vs D) at all determined budgets"],
    "unresolved": [],
    "attempts": 2,
    "selected_attempt": 1,
    "stop_reason": "max_attempts",
    "oscillated": False,
    "attempt_lines": ["attempt 0: mismatch", "attempt 1: mismatch"],
    "judge_kind": "underdetermined",
    "judge_notes": "could not settle from the term",
}


def test_request_exposes_review_knobs() -> None:
    req = PipelineRequest(bot_a={"name": "X", "strategy": "s"})
    assert req.review_bots is True, "review is on by default"
    assert req.max_rewrites == 2

    off = PipelineRequest(bot_a={"name": "X", "strategy": "s"},
                          review_bots=False, max_rewrites=0)
    assert off.review_bots is False and off.max_rewrites == 0


def test_review_survives_serialisation_into_job_response() -> None:
    job = Job(job_id="t", status=JobStatus.bots_ready)
    job.bot_a_draft = BotResult("X", "-- src", 1)
    job.bot_a_review = _REVIEW

    review = job.to_response_dict()["bot_a"].review
    assert review is not None
    assert review.verdict == "mismatch"
    assert review.hard_failures == 1
    assert review.attempts == 2 and review.selected_attempt == 1
    assert review.cells[0].opponent == "DefectBot"
    assert review.judge_kind == "underdetermined"


def test_missing_review_is_allowed() -> None:
    """Review is advisory: a job without one must still serialise."""
    job = Job(job_id="t", status=JobStatus.bots_ready)
    job.bot_a_draft = BotResult("X", "-- src", 1)

    assert job.to_response_dict()["bot_a"].review is None


def test_ui_ships_the_review_controls_and_renderer() -> None:
    html = TestClient(app).get("/").text
    assert "review-select" in html, "no faithfulness control in the form"
    assert "renderReview" in html, "no renderer for the review block"
    assert "review_bots" in html, "the form never sends the review flag"
    assert "max_rewrites" in html, "the form never sends the rewrite budget"
    # The judge must stay labelled as advisory wherever it is shown.
    assert "advisory" in html.lower()

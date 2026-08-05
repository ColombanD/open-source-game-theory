"""The rewriter loop: generate → review → feed the mismatch back → re-review.

Design note: `docs/BOT_REVIEWER.md` §7. Read it before changing the trigger,
the feedback content, or the termination conditions — each is load-bearing and
the reasons are not obvious from the code.

The short version of the invariants:

  * **Trigger only on strong evidence** (`comparison.should_rewrite` =
    explicit mismatch or unanimous mismatch). Never on `inferred` warnings,
    `unspecified`/`uncertified` cells, or ANY Tier B verdict — the judge has no
    ground truth, so it must not drive an automatic code change.
  * **Extract the expectation ONCE** and reuse it across attempts. Re-extracting
    per attempt lets the prediction drift toward whatever the bot currently
    does, which destroys the independence the whole review rests on. Enforced by
    `evaluate_against`, which structurally cannot extract its own expectation.
  * **Feed back failures, not the answer key** — `mismatch_brief()` carries only
    the failing cells. Handing over the full certified profile invites fitting
    the four canonical opponents rather than implementing the strategy.
  * **Never auto-accept.** This improves what the human sees at the gate; it
    does not replace the gate.
"""

from __future__ import annotations

from dataclasses import dataclass
from datetime import datetime

from pd_runner import settings
from pd_runner.logging_config import get_logger
from pd_runner.services.bot_expectation import (
    Expectation,
    ReviewComparison,
    evaluate_against,
    extract_expectation,
    persist_review,
)
from pd_runner.services.bot_profile import CANONICAL_OPPONENTS, BotProfile
from pd_runner.services.bot_service import BotRequest, BotResult, BotWriteError, search_bot

_log = get_logger("services.bot_rewriter")

DEFAULT_MAX_REWRITES = 2


@dataclass(frozen=True)
class Attempt:
    """One generate-and-review round."""

    index: int
    bot: BotResult
    profile: BotProfile
    comparison: ReviewComparison

    @property
    def hard_failures(self) -> int:
        return len(self.comparison.hard_failures)

    def summary(self) -> str:
        tag = "initial" if self.index == 0 else f"rewrite {self.index}"
        return (
            f"attempt {self.index} ({tag}): {self.comparison.verdict}"
            f", {self.hard_failures} hard failure(s)"
            f", coverage {len(self.profile.determined_cells)}/{len(self.profile.cells)}"
        )


@dataclass(frozen=True)
class RewriteRun:
    """Every attempt, plus the one to show the human."""

    bot_name: str
    expectation: Expectation
    attempts: tuple[Attempt, ...]
    best: Attempt
    stop_reason: str  # faithful | max_attempts | no_behavior_change | writer_failed

    @property
    def improved(self) -> bool:
        return len(self.attempts) > 1 and self.best.index > 0

    @property
    def oscillated(self) -> bool:
        """Behavior returned to an earlier state — the description is ambiguous.

        A finding about the DESCRIPTION, not a defect in the bot.
        """
        keys = [a.profile.behavior_key() for a in self.attempts]
        return len(keys) != len(set(keys))

    def render(self) -> str:
        lines = [f"Rewrite run — {self.bot_name} ({self.stop_reason})"]
        for a in self.attempts:
            marker = " <- selected" if a is self.best else ""
            lines.append(f"  {a.summary()}{marker}")
        if self.oscillated:
            lines.append(
                "  NOTE: behavior repeated across attempts — the description may be "
                "ambiguous about the disputed cells."
            )
        return "\n".join(lines)


def review_payload(run: RewriteRun, judge=None) -> dict:
    """Flatten a run into the shape the API's `BotReview` expects.

    Kept next to the loop rather than in the API layer so the CLI and the web
    app cannot drift about what a review "is". `judge` is an optional
    `JudgeReview` — ADVISORY, never an acceptance criterion.
    """
    best = run.best
    comparison, profile = best.comparison, best.profile
    return {
        "verdict": comparison.verdict,
        "summary": run.expectation.summary,
        "cells": [
            {
                "opponent": c.opponent, "kind": c.kind, "expected": c.expected,
                "expected_confidence": c.expected_confidence, "actual": c.actual,
                "detail": c.detail,
            }
            for c in comparison.cells
        ],
        "hard_failures": len(comparison.hard_failures),
        "warnings": len(comparison.warnings),
        "unanimous_mismatch": comparison.unanimous_mismatch,
        "coverage": (
            f"{len(profile.determined_cells)}/{len(profile.cells)} opponents certified"
        ),
        "profile_lines": [f"vs {c.opponent}: {c.describe()}" for c in profile.cells],
        "unresolved": list(comparison.unresolved),
        "attempts": len(run.attempts),
        "selected_attempt": best.index,
        "stop_reason": run.stop_reason,
        "oscillated": run.oscillated,
        "attempt_lines": [a.summary() for a in run.attempts],
        "judge_kind": getattr(judge, "kind", None),
        "judge_notes": getattr(judge, "notes", None) or None,
    }


def rewrite_until_faithful(
    bot_name: str,
    strategy_description: str,
    initial: BotResult,
    *,
    max_rewrites: int = DEFAULT_MAX_REWRITES,
    opponents: tuple[str, ...] = CANONICAL_OPPONENTS,
    model: str = settings.DEFAULT_MODEL,
    max_iterations: int = settings.DEFAULT_MAX_ITERATIONS,
    max_tokens: int = settings.DEFAULT_MAX_TOKENS,
    thinking_effort: str = settings.DEFAULT_THINKING_EFFORT,
    persist: bool = True,
    progress=None,
) -> RewriteRun:
    """Review `initial`, and rewrite it while the evidence justifies rewriting.

    Returns every attempt plus the best one. NEVER writes to the library — the
    human acceptance gate is unchanged; this only improves what reaches it.

    Each attempt costs one bot-writer run plus a ~25-55s certified sweep, so the
    default budget is deliberately small.
    """
    run_ts = datetime.now().strftime("%Y%m%dT%H%M%S")

    def note(msg: str) -> None:
        _log.info("%s", msg)
        if progress is not None:
            progress(msg)

    # ONCE. Never re-extracted — see the module docstring.
    expectation = extract_expectation(
        strategy_description, opponents=opponents, model=model
    )
    note(f"blind expectation for {bot_name}: {expectation.summary}")

    def review(bot: BotResult, index: int) -> Attempt:
        profile, comparison = evaluate_against(
            bot.bot_name, bot.lean_source, expectation, opponents=opponents,
        )
        attempt = Attempt(index=index, bot=bot, profile=profile, comparison=comparison)
        if persist:
            persist_review(
                bot_name, strategy_description, bot.lean_source,
                expectation, profile, comparison, attempt=index, run_ts=run_ts,
            )
        note(attempt.summary())
        return attempt

    attempts = [review(initial, 0)]
    stop_reason = ""

    while attempts[-1].comparison.should_rewrite:
        if len(attempts) > max_rewrites:
            stop_reason = "max_attempts"
            break

        note(f"rewriting {bot_name} (attempt {len(attempts)}) — feeding back mismatches")
        try:
            nxt = search_bot(BotRequest(
                bot_name=bot_name,
                strategy_description=strategy_description,
                model=model,
                max_iterations=max_iterations,
                max_tokens=max_tokens,
                thinking_effort=thinking_effort,
                feedback=attempts[-1].comparison.mismatch_brief(),
            ))
        except BotWriteError as exc:
            note(f"rewrite failed to produce a compiling bot: {exc}")
            stop_reason = "writer_failed"
            break

        attempt = review(nxt, len(attempts))

        # Compare BEHAVIOR, not the profile object: BotProfile.__eq__ includes
        # per-cell wall-clock timings, so `==` would never report "unchanged".
        if attempt.profile.behavior_key() == attempts[-1].profile.behavior_key():
            attempts.append(attempt)
            note("rewrite did not change behavior — the writer did not act on the feedback")
            stop_reason = "no_behavior_change"
            break

        attempts.append(attempt)

    # Loop fell through its condition: the last attempt no longer wants rewriting.
    if not stop_reason:
        stop_reason = "faithful"

    # Fewest hard failures wins; ties go to the EARLIER attempt (a rewrite has to
    # earn its place, and the initial bot is the one the writer reasoned about
    # with the full description rather than a mismatch list).
    best = min(attempts, key=lambda a: (a.hard_failures, a.index))
    return RewriteRun(
        bot_name=bot_name,
        expectation=expectation,
        attempts=tuple(attempts),
        best=best,
        stop_reason=stop_reason,
    )

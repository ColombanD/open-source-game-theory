"""Tier A1 of the bot reviewer: the BLIND expectation extractor.

Turns a natural-language strategy description into a predicted behavioral
profile against the canonical opponents — **without ever seeing the generated
Lean**. That blindness is the entire point, and it is enforced by the call
signature: `extract_expectation` takes the NL string, never a `BotResult`.

Why it matters. A judge that reads the generated source AND the description and
rules "yes, these match" is re-deriving the bot writer's own reasoning, from the
same model family, with the same blind spots, over the same text. It is
correlated with the generator in exactly the way that makes LLM judges fail, and
the failure modes that actually bite here (probe target frozen vs substituted,
guard polarity inverted, `.self`/`.opp` swapped) are precisely the ones where a
plausible-sounding rationale reads fine. Predicting behavior from the NL alone
breaks that correlation, and it is the only formulation that yields a defensible
number for Phase-4 E2b ("behaves as described"): the prediction must not be
derived from the answer.

Two fields carry most of the design weight:

  * `unspecified` is a FIRST-CLASS answer. Most NL descriptions genuinely do not
    determine all four cells ("cooperates with nice bots" says nothing about
    TitForTatBot). An extractor pressured into guessing manufactures false
    mismatches, which is the fastest way to make the whole reviewer ignorable.
    Unspecified cells are reported as coverage, never as failure.
  * `confidence` separates `explicit` ("the description literally says it
    defects against defectors") from `inferred` ("a bot described as retaliatory
    presumably defects against DefectBot"). Only `explicit` mismatches are
    hard failures; `inferred` ones are warnings. Without this split the
    reviewer's false-positive rate is set by how aggressively the extractor
    extrapolates.

The comparison against the certified Tier-A2 profile lives in `compare()` and is
pure deterministic code — no judge, no calibration, nothing to trust.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

from pd_runner import settings
from pd_runner.llm.client import EpisodeStop, ToolHandler
from pd_runner.llm.factory import make_llm_client
from pd_runner.logging_config import TRACE, get_logger
from pd_runner.services.bot_profile import (
    CANONICAL_OPPONENTS,
    BotProfile,
    build_profile,
    staged_bot,
)

_log = get_logger("services.bot_expectation")

Action = Literal["C", "D", "unspecified"]
Confidence = Literal["explicit", "inferred"]
MatchKind = Literal["match", "mismatch", "unspecified", "uncertified"]

# How each canonical opponent BEHAVES, in words. The extractor reasons about
# behavior, never about `Prog` syntax — handing it Program.lean would push it to
# predict Lean terms and re-couple it to the writer it is supposed to check.
_OPPONENT_BRIEF = {
    "CooperateBot": "always cooperates, unconditionally. It never inspects you.",
    "DefectBot": "always defects, unconditionally. It never inspects you.",
    "MirrorBot": (
        "simulates you against itself and plays whatever you would play against it "
        "— a perfect imitator, so it cooperates with cooperators and defects "
        "against defectors."
    ),
    "TitForTatBot": (
        "simulates you against a cooperator and copies that: it cooperates if you "
        "would cooperate with a cooperative opponent, and defects otherwise."
    ),
}


@dataclass(frozen=True)
class ExpectedCell:
    opponent: str
    my_action: Action
    confidence: Confidence
    rationale: str

    @property
    def is_specified(self) -> bool:
        return self.my_action in ("C", "D")


@dataclass(frozen=True)
class Expectation:
    """What the NL description predicts, before any Lean is seen."""

    cells: tuple[ExpectedCell, ...]
    structural_claims: tuple[str, ...] = ()
    summary: str = ""

    def cell(self, opponent: str) -> ExpectedCell | None:
        return next((c for c in self.cells if c.opponent == opponent), None)

    @property
    def specified_cells(self) -> tuple[ExpectedCell, ...]:
        return tuple(c for c in self.cells if c.is_specified)

    def render(self) -> str:
        width = max((len(c.opponent) for c in self.cells), default=10) + 2
        lines = ["Expected behavior (from the description alone):"]
        for c in self.cells:
            action = c.my_action if c.is_specified else "unspecified"
            tag = "" if not c.is_specified else f" [{c.confidence}]"
            lines.append(f"  vs {c.opponent:<{width}} {action}{tag} — {c.rationale}")
        if self.structural_claims:
            lines.append("  structural claims (not decidable from a 4-cell profile):")
            lines.extend(f"    - {s}" for s in self.structural_claims)
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# The comparison — deterministic, no LLM
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CellComparison:
    opponent: str
    kind: MatchKind
    expected: str | None
    expected_confidence: Confidence | None
    actual: str | None
    detail: str

    @property
    def is_hard_failure(self) -> bool:
        """Only an EXPLICIT mismatch is a hard failure (see module docstring)."""
        return self.kind == "mismatch" and self.expected_confidence == "explicit"


@dataclass(frozen=True)
class ReviewComparison:
    bot_name: str
    cells: tuple[CellComparison, ...]
    unresolved: tuple[str, ...] = ()

    @property
    def hard_failures(self) -> tuple[CellComparison, ...]:
        return tuple(c for c in self.cells if c.is_hard_failure)

    @property
    def warnings(self) -> tuple[CellComparison, ...]:
        return tuple(
            c for c in self.cells
            if c.kind == "mismatch" and c.expected_confidence != "explicit"
        )

    @property
    def checked(self) -> tuple[CellComparison, ...]:
        return tuple(c for c in self.cells if c.kind in ("match", "mismatch"))

    @property
    def mismatches(self) -> tuple[CellComparison, ...]:
        return tuple(c for c in self.cells if c.kind == "mismatch")

    @property
    def unanimous_mismatch(self) -> bool:
        """Every checked cell contradicts the description.

        Individually an `inferred` mismatch is only a warning — the extractor
        extrapolated, so it may have extrapolated wrong. But if EVERY certified
        cell disagrees, the aggregate is not a shaky inference any more: no
        plausible reading of the description survives four out of four
        contradictions. Caught in review of an inverted-polarity GuardianBot,
        where four `inferred` mismatches summed to a `faithful` verdict.

        Requires at least two checked cells: one lone inferred mismatch is
        exactly the weak evidence the confidence split exists to discount.
        """
        return len(self.checked) >= 2 and len(self.mismatches) == len(self.checked)

    @property
    def verdict(self) -> Literal["faithful", "mismatch", "underdetermined"]:
        if self.hard_failures or self.unanimous_mismatch:
            return "mismatch"
        if not self.checked:
            return "underdetermined"
        return "faithful"

    @property
    def should_rewrite(self) -> bool:
        """Is the evidence strong enough to send this back to the bot writer?

        THE single place the "never rewrite on weak evidence" rule lives
        (docs/BOT_REVIEWER.md §7). Deliberately NOT triggered by: `inferred`
        mismatches on their own (the extractor extrapolated and may have
        extrapolated wrong), `unspecified` cells (the description is silent —
        that is not the bot's fault), `uncertified` cells (absence of proof is
        not proof of a defect), or ANY Tier B verdict (the judge has no ground
        truth, so it must never drive an automatic code change).
        """
        return bool(self.hard_failures) or self.unanimous_mismatch

    def mismatch_brief(self) -> str:
        """The feedback handed to the bot writer on a rewrite.

        Carries ONLY the failing cells — never the full certified profile.
        Handing over every cell invites fitting the four canonical opponents
        instead of implementing the described strategy, producing a bot that
        passes the reviewer while being no more faithful. Report the failures,
        not the answer key.
        """
        lines = []
        for c in self.mismatches:
            lines.append(
                f"- Against {c.opponent}: the description implies your bot plays "
                f"{c.expected}, but it certifiably plays {c.actual}."
            )
            if c.expected_confidence == "explicit":
                lines.append("    (the description states this case directly)")
        if self.unanimous_mismatch and not self.hard_failures:
            lines.append(
                "\nEvery cell that could be checked disagrees with the description, "
                "which usually means the strategy's core logic is inverted rather "
                "than one case being wrong."
            )
        return "\n".join(lines)

    @property
    def needs_judge(self) -> bool:
        """True when Tier B has something only it can rule on."""
        return bool(self.unresolved) or any(
            c.kind in ("unspecified", "uncertified") for c in self.cells
        )

    def render(self) -> str:
        symbol = {"match": "OK ", "mismatch": "MISMATCH", "unspecified": "-  ",
                  "uncertified": "?  "}
        width = max((len(c.opponent) for c in self.cells), default=10) + 2
        lines = [f"Faithfulness check — {self.bot_name}: {self.verdict.upper()}"]
        for c in self.cells:
            lines.append(f"  {symbol[c.kind]:<9} vs {c.opponent:<{width}} {c.detail}")
        if self.warnings:
            lines.append(
                f"  ({len(self.warnings)} inferred-only mismatch(es) — warnings, not failures)"
            )
        if self.unresolved:
            lines.append("  for the judge:")
            lines.extend(f"    - {u}" for u in self.unresolved)
        return "\n".join(lines)


def compare(expectation: Expectation, profile: BotProfile) -> ReviewComparison:
    """Deterministically check the blind prediction against certified behavior."""
    cells: list[CellComparison] = []

    for expected in expectation.cells:
        actual_cell = profile.cell(expected.opponent)

        if not expected.is_specified:
            cells.append(CellComparison(
                opponent=expected.opponent, kind="unspecified",
                expected=None, expected_confidence=None,
                actual=actual_cell.my_action if actual_cell else None,
                detail=(
                    "description does not determine this cell"
                    + (f"; engine says {actual_cell.describe()}" if actual_cell else "")
                ),
            ))
            continue

        if actual_cell is None or actual_cell.verdict == "undetermined":
            note = actual_cell.note if actual_cell else "not evaluated"
            cells.append(CellComparison(
                opponent=expected.opponent, kind="uncertified",
                expected=expected.my_action, expected_confidence=expected.confidence,
                actual=None,
                detail=f"expected {expected.my_action}, but the engine could not certify ({note})",
            ))
            continue

        # A budget phase transition is NOT a mismatch: "cooperates until it can
        # prove things, then defects" is often exactly what the NL described.
        # Whether the ladder matches the description is a judge question.
        if actual_cell.verdict == "phase_dependent":
            cells.append(CellComparison(
                opponent=expected.opponent, kind="uncertified",
                expected=expected.my_action, expected_confidence=expected.confidence,
                actual=None,
                detail=(
                    f"expected {expected.my_action}; engine says {actual_cell.describe()} "
                    "— budget-dependent, needs interpretation"
                ),
            ))
            continue

        matched = actual_cell.my_action == expected.my_action
        cells.append(CellComparison(
            opponent=expected.opponent,
            kind="match" if matched else "mismatch",
            expected=expected.my_action,
            expected_confidence=expected.confidence,
            actual=actual_cell.my_action,
            detail=(
                f"expected {expected.my_action}, engine certifies {actual_cell.my_action}"
                + ("" if matched else f"  <-- {expected.confidence} claim: {expected.rationale}")
            ),
        ))

    unresolved = list(expectation.structural_claims)
    for c in cells:
        if c.kind == "uncertified":
            unresolved.append(f"vs {c.opponent}: {c.detail}")

    return ReviewComparison(
        bot_name=profile.bot_name, cells=tuple(cells), unresolved=tuple(unresolved)
    )


# ---------------------------------------------------------------------------
# The extractor agent
# ---------------------------------------------------------------------------


def persist_review(
    bot_name: str,
    strategy_description: str,
    lean_source: str,
    expectation: Expectation,
    profile: BotProfile,
    comparison: ReviewComparison,
    *,
    attempt: int = 0,
    run_ts: str | None = None,
    judge: dict[str, Any] | None = None,
) -> Path:
    """Append one review attempt to `generated/reviews/<bot>_<ts>.jsonl`.

    Longitudinal data for Phase-4 E2: did rewriting help, how often, did a bot
    oscillate between attempts? One row per attempt, never deleted, mirroring
    how `generated/outcomes/` preserves proof episodes.

    `run_ts` groups the attempts of one rewrite run; pass the same value for
    every attempt. Timestamps are stamped here rather than threaded in, so a
    caller cannot accidentally group unrelated runs.
    """
    from datetime import datetime

    from pd_runner.config import load_paths

    ts = run_ts or datetime.now().strftime("%Y%m%dT%H%M%S")
    d = load_paths().app_root / "generated" / "reviews"
    d.mkdir(parents=True, exist_ok=True)
    path = d / f"{bot_name}_{ts}.jsonl"

    row = {
        "timestamp": ts,
        "bot_name": bot_name,
        "attempt": attempt,
        "strategy_description": strategy_description,
        "lean_source": lean_source,
        "verdict": comparison.verdict,
        "should_rewrite": comparison.should_rewrite,
        "unanimous_mismatch": comparison.unanimous_mismatch,
        "hard_failures": len(comparison.hard_failures),
        "warnings": len(comparison.warnings),
        "coverage": profile.coverage,
        "behavior_key": [list(k) for k in profile.behavior_key()],
        "expectation": {
            "summary": expectation.summary,
            "structural_claims": list(expectation.structural_claims),
            "cells": [
                {"opponent": c.opponent, "my_action": c.my_action,
                 "confidence": c.confidence, "rationale": c.rationale}
                for c in expectation.cells
            ],
        },
        "cells": [
            {"opponent": c.opponent, "kind": c.kind, "expected": c.expected,
             "expected_confidence": c.expected_confidence, "actual": c.actual,
             "detail": c.detail}
            for c in comparison.cells
        ],
        "profile_cells": [
            {"opponent": c.opponent, "verdict": c.verdict, "my_action": c.my_action,
             "by_budget": {str(k): v for k, v in c.by_budget.items()}, "note": c.note}
            for c in profile.cells
        ],
        "unresolved": list(comparison.unresolved),
        "judge": judge,
    }
    with path.open("a") as fh:
        fh.write(json.dumps(row) + "\n")
    _log.info("persisted review attempt %d for %s -> %s", attempt, bot_name, path)
    return path


def evaluate_against(
    bot_name: str,
    lean_source: str,
    expectation: Expectation,
    *,
    opponents: tuple[str, ...] = CANONICAL_OPPONENTS,
    already_in_library: bool = False,
    progress=None,
) -> tuple[BotProfile, ReviewComparison]:
    """Profile a bot and compare it against an ALREADY-EXTRACTED expectation.

    Split out of `review_bot` so the rewriter can extract the expectation ONCE
    and reuse it across attempts. Re-extracting per attempt would let the
    prediction drift toward whatever the bot currently does, quietly destroying
    the independence the whole design rests on — passing the expectation in
    makes "extract once" enforceable by the signature rather than a convention
    someone has to remember.

    `already_in_library=True` profiles the bot by name (it is on disk already);
    otherwise the source is staged temporarily so a not-yet-accepted bot can be
    profiled without being written to the library.
    """
    if already_in_library:
        profile = build_profile(bot_name, opponents=opponents, progress=progress)
    else:
        with staged_bot(bot_name, lean_source) as module:
            profile = build_profile(
                bot_name, lean_source=lean_source, module=module,
                opponents=opponents, progress=progress,
            )
    return profile, compare(expectation, profile)


def review_bot(
    bot_name: str,
    strategy_description: str,
    lean_source: str,
    *,
    opponents: tuple[str, ...] = CANONICAL_OPPONENTS,
    model: str = settings.DEFAULT_MODEL,
    already_in_library: bool = False,
    progress=None,
) -> tuple[Expectation, BotProfile, ReviewComparison]:
    """Tier A end to end: blind prediction + certified profile + comparison.

    The prediction is extracted BEFORE the profile is computed and never sees
    `lean_source` — `lean_source` is used only to make the bot importable.
    """
    expectation = extract_expectation(
        strategy_description, opponents=opponents, model=model
    )
    _log.info("blind expectation for %s: %s", bot_name, expectation.summary)

    profile, comparison = evaluate_against(
        bot_name, lean_source, expectation,
        opponents=opponents, already_in_library=already_in_library,
        progress=progress,
    )
    return expectation, profile, comparison


def _submit_tool(opponents: tuple[str, ...]) -> dict[str, Any]:
    return {
        "name": "submit_expectation",
        "description": (
            "Submit your predicted behavior profile. This is the ONLY way to finish. "
            "Predict what the DESCRIBED strategy would do — you have not been shown any "
            "implementation, and you must not guess at one. If the description does not "
            "determine a cell, answer 'unspecified': that is a correct and expected "
            "answer, and guessing instead creates false alarms."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "cells": {
                    "type": "array",
                    "description": f"One entry per opponent: {', '.join(opponents)}.",
                    "items": {
                        "type": "object",
                        "properties": {
                            "opponent": {"type": "string", "enum": list(opponents)},
                            "my_action": {
                                "type": "string",
                                "enum": ["C", "D", "unspecified"],
                                "description": (
                                    "What the DESCRIBED bot plays against this opponent. "
                                    "'unspecified' when the description does not settle it."
                                ),
                            },
                            "confidence": {
                                "type": "string",
                                "enum": ["explicit", "inferred"],
                                "description": (
                                    "'explicit': the description states this case directly. "
                                    "'inferred': you extrapolated from the general strategy. "
                                    "Be honest — only explicit claims are treated as hard "
                                    "requirements."
                                ),
                            },
                            "rationale": {
                                "type": "string",
                                "description": "One sentence, quoting the description where possible.",
                            },
                        },
                        "required": ["opponent", "my_action", "confidence", "rationale"],
                    },
                },
                "structural_claims": {
                    "type": "array",
                    "items": {"type": "string"},
                    "description": (
                        "Claims in the description about HOW the bot decides that a "
                        "four-cell behavior profile could not distinguish (e.g. 'punishes "
                        "via a third-party probe rather than direct reciprocity'). Empty "
                        "if the description is purely behavioral."
                    ),
                },
                "summary": {
                    "type": "string",
                    "description": "One sentence restating the strategy in your own words.",
                },
            },
            "required": ["cells", "summary"],
        },
    }


def _system_prompt(opponents: tuple[str, ...]) -> str:
    briefs = "\n".join(
        f"- **{o}**: {_OPPONENT_BRIEF.get(o, 'see the library definition.')}"
        for o in opponents
    )
    return f"""\
You predict how a described Prisoner's Dilemma strategy will BEHAVE.

You are given ONLY a natural-language strategy description. You will NOT be shown
any implementation, and you must not speculate about one — your job is to say what
the description itself commits to. Another process independently computes what the
implementation actually does; the two are compared to detect translation errors.
If you guess at implementation details, that comparison stops being meaningful.

# The opponents

Each match is one-shot. Both players' source code is visible to the other, so a
strategy may inspect or simulate its opponent before choosing. Actions are
C (cooperate) and D (defect).

{briefs}

# How to answer

For each opponent, say what the DESCRIBED strategy plays: C, D, or `unspecified`.

`unspecified` is a correct, expected, and frequently right answer. Descriptions
are usually partial — "cooperates with nice bots, punishes bullies" simply does
not settle what happens against a perfect imitator. Answer `unspecified` rather
than reasoning your way to a guess. A wrong guess raises a false alarm against a
correct implementation, which is worse than admitting the description is silent.

Mark each specified cell `explicit` (the description addresses this case directly,
e.g. "always defects against DefectBot") or `inferred` (you extrapolated from the
general policy). Be strict: if you had to reason more than one step, it is
`inferred`. Only explicit claims are treated as hard requirements.

Put anything about the bot's INTERNAL MECHANISM — how it decides, what it probes,
what it reasons about — in `structural_claims`, not in the cells. Those are checked
separately, because two very different mechanisms can produce identical behavior.

Call `submit_expectation` exactly once. Do not write prose outside the tool call.
"""


def extract_expectation(
    strategy_description: str,
    *,
    opponents: tuple[str, ...] = CANONICAL_OPPONENTS,
    model: str = settings.DEFAULT_MODEL,
    max_tokens: int = 8_000,
    thinking_effort: str = settings.DEFAULT_THINKING_EFFORT,
) -> Expectation:
    """Predict the described strategy's behavior WITHOUT seeing any Lean.

    The signature takes the description string, never a `BotResult`: blindness
    is a structural property of this function, not a convention to remember.
    """
    handler = ToolHandler()
    captured: dict[str, Any] = {}

    def submit_expectation(**payload: Any) -> EpisodeStop:
        captured.update(payload)
        return EpisodeStop(
            payload=payload,
            confirmation_text="Expectation recorded.",
            end_reason="expectation",
        )

    handler.register_fn("submit_expectation", submit_expectation)

    client = make_llm_client(
        system_prompt=_system_prompt(opponents),
        tools=[_submit_tool(opponents)],
        model=model,
        max_iterations=4,
        max_tokens=max_tokens,
        thinking_effort=thinking_effort,
    )

    user_message = (
        f"Strategy description:\n\n{strategy_description.strip()}\n\n"
        f"Predict this strategy's action against each of: {', '.join(opponents)}. "
        "Use `unspecified` wherever the description does not settle the answer."
    )
    _log.log(TRACE, "expectation extractor user message:\n%s", user_message)

    result = client.run_episode(
        user_message, handler, max_turns=4, stop_tool="submit_expectation"
    )
    payload = result.verdict_input or captured
    if not payload:
        raise RuntimeError(
            "expectation extractor did not submit a prediction "
            f"(end_reason={result.end_reason})"
        )

    by_opponent = {
        c["opponent"]: c for c in payload.get("cells", []) if c.get("opponent") in opponents
    }
    cells = tuple(
        ExpectedCell(
            opponent=o,
            my_action=by_opponent.get(o, {}).get("my_action", "unspecified"),
            confidence=by_opponent.get(o, {}).get("confidence", "inferred"),
            rationale=by_opponent.get(o, {}).get(
                "rationale", "not addressed by the extractor"
            ),
        )
        for o in opponents
    )
    return Expectation(
        cells=cells,
        structural_claims=tuple(payload.get("structural_claims") or ()),
        summary=payload.get("summary", ""),
    )

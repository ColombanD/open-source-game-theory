"""Tier B of the bot reviewer: the judge agent, on the RESIDUAL only.

Read this caveat before using anything here:

    TIER B HAS NO GROUND TRUTH. It is advisory input to the human acceptance
    gate, never an acceptance criterion, and its verdicts must NOT be reported
    as verification results. Tier A2's certified cells are theorems; a judge's
    opinion is an opinion, produced by a model from the same family as the one
    that wrote the bot. The honest experiment for measuring it is to hand-label
    N generated bots and publish the judge's agreement rate against those
    labels; until that exists, treat Tier B output as a hint.

It fires only where Tier A cannot decide:

  * `uncertified` cells — the fast decider did not commit (Löb boundary, budget
    floor, guard shape beyond `guardFastN`, or a 90s timeout);
  * `phase_dependent` cells — the outcome is genuinely budget-dependent, and
    whether that ladder matches the description needs interpretation, not a
    comparison ("cooperates until it can prove things, then defects" may be
    exactly right);
  * `structural_claims` — assertions about the MECHANISM that no four-cell
    behavioral profile could separate. GuardianBot punishes bullies via a
    frozen third-party probe; a direct-reciprocity bot could produce an
    identical profile against these four opponents. Only reading the term
    settles it.

Cells Tier A already decided are NOT re-litigated: a certified `match` or an
explicit `mismatch` is stronger evidence than anything the judge can offer, and
inviting it to second-guess them is how a judge starts overturning theorems.
They are passed as context, clearly marked as settled.

`underdetermined` is a respectable verdict here, exactly as `open_bistable` is
for the proof agent. A judge with no honest way to say "I cannot tell from this"
will invent something.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Literal

from pd_runner import settings
from pd_runner.llm.client import EpisodeStop, ToolHandler
from pd_runner.llm.factory import make_llm_client
from pd_runner.llm.tools import _READ_LIBRARY_FILE_TOOL, _SEARCH_LIBRARY_TOOL, _read_library_file
from pd_runner.logging_config import TRACE, get_logger
from pd_runner.services.bot_expectation import Expectation, ReviewComparison
from pd_runner.services.bot_profile import BotProfile

_log = get_logger("services.bot_judge")

ReviewKind = Literal["faithful", "mismatch", "underdetermined"]
Severity = Literal["blocking", "concern", "note"]


@dataclass(frozen=True)
class Discrepancy:
    claim: str          # what the description asserts
    expected: str       # what that implies
    actual: str         # what the Lean term does
    severity: Severity
    evidence: str       # the specific sub-term / line that settles it


@dataclass(frozen=True)
class JudgeReview:
    kind: ReviewKind
    discrepancies: tuple[Discrepancy, ...] = ()
    unresolved: tuple[str, ...] = ()
    notes: str = ""

    @property
    def blocking(self) -> tuple[Discrepancy, ...]:
        return tuple(d for d in self.discrepancies if d.severity == "blocking")

    def render(self) -> str:
        lines = [f"Judge review (ADVISORY — no ground truth): {self.kind.upper()}"]
        for d in self.discrepancies:
            lines.append(f"  [{d.severity}] {d.claim}")
            lines.append(f"      implies: {d.expected}")
            lines.append(f"      actual:  {d.actual}")
            if d.evidence:
                lines.append(f"      evidence: {d.evidence}")
        if self.unresolved:
            lines.append("  could not determine:")
            lines.extend(f"    - {u}" for u in self.unresolved)
        if self.notes:
            lines.append(f"  notes: {self.notes}")
        return "\n".join(lines)


_SUBMIT_TOOL: dict[str, Any] = {
    "name": "submit_review",
    "description": (
        "Submit your FINAL judgement on the open questions. This is the ONLY way to "
        "finish. If the evidence does not settle a question, say so via `unresolved` "
        "and use the `underdetermined` verdict — that is a respectable answer and is "
        "strongly preferred over inventing a conclusion."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            "kind": {
                "type": "string",
                "enum": ["faithful", "mismatch", "underdetermined"],
                "description": (
                    "`faithful`: the open questions resolve in the implementation's "
                    "favour. `mismatch`: the term demonstrably contradicts the "
                    "description. `underdetermined`: the evidence does not settle it."
                ),
            },
            "discrepancies": {
                "type": "array",
                "items": {
                    "type": "object",
                    "properties": {
                        "claim": {"type": "string", "description": "What the description asserts, quoted."},
                        "expected": {"type": "string", "description": "What that claim implies the bot should do."},
                        "actual": {"type": "string", "description": "What the Lean term actually does."},
                        "severity": {
                            "type": "string",
                            "enum": ["blocking", "concern", "note"],
                            "description": (
                                "`blocking`: the bot does not implement the described "
                                "strategy. `concern`: arguable divergence. `note`: "
                                "worth mentioning, not a defect."
                            ),
                        },
                        "evidence": {
                            "type": "string",
                            "description": (
                                "The specific sub-term that settles it, e.g. "
                                "'.plays .opp .self Action.D in the guard' — not a "
                                "restatement of your reasoning."
                            ),
                        },
                    },
                    "required": ["claim", "expected", "actual", "severity", "evidence"],
                },
            },
            "unresolved": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Open questions you could NOT settle, and why.",
            },
            "notes": {"type": "string", "description": "One or two sentences of context."},
        },
        "required": ["kind"],
    },
}

_SYSTEM_PROMPT = """\
You are reviewing whether a Lean 4 bot faithfully implements a natural-language
strategy description, in the open-source game theory (OSGT) setting.

Both players' source code is visible to the other, so a bot may inspect, simulate,
or run bounded proof search about its opponent before choosing C or D.

# Your scope: the OPEN questions only

A certified evaluator has ALREADY decided most of this, by machine proof. Those
cells are settled and are given to you as context — do NOT re-litigate them. Your
job is only the residual the evaluator could not decide:

  1. **Uncertified cells** — the decider could not commit (a Löb boundary, a cost
     floor, a guard shape it cannot handle, or a timeout). Read the term and say
     what it does against that opponent, if the term settles it.
  2. **Budget-dependent cells** — the outcome genuinely changes with the proof
     budget. This is NOT automatically a defect: "cooperates until it can prove
     otherwise, then defects" is a real strategy, and a bot whose behavior shifts
     at higher budgets may match the description perfectly. Judge whether the
     LADDER matches the description, not whether one sample does.
  3. **Structural claims** — assertions about HOW the bot decides that behavior
     alone cannot distinguish. Two mechanisms can produce identical profiles
     against four opponents. Read the term.

# What actually goes wrong

These are the failure modes worth looking for — all compile, all read plausibly:

  - the probe target is FROZEN (`.bot SomeBot`, which `subst` will not descend
    into) where the description implies the actual opponent (`.opp`), or vice versa;
  - `.self` and `.opp` swapped inside a `.plays` atom — "you cooperate with me"
    versus "I cooperate with you";
  - guard polarity inverted: the then-branch and else-branch exchanged;
  - `.neg (.plays ... C)` where the description means "can prove it defects" —
    semantically equal with two actions, but proved through different machinery;
  - a search budget that cannot pay for what the description requires.

Use `read_library_file` and `search_library` to check how existing bots express
the same idea before ruling — e.g. how JustBot freezes its probe target.

# How to answer

Cite the specific sub-term that settles each point. "The guard reads
`.plays .opp .self Action.D`, which asserts the OPPONENT defects against ME" is
evidence; "the bot seems to implement the strategy" is not.

If the term does not settle a question, say so in `unresolved` and return
`underdetermined`. You are advisory input to a human reviewer, not the last word,
and a confident wrong answer is far worse here than an honest "I cannot tell".

Call `submit_review` exactly once. Do not write prose outside the tool call.
"""


def _residual_brief(
    bot_name: str,
    strategy_description: str,
    lean_source: str,
    expectation: Expectation,
    profile: BotProfile,
    comparison: ReviewComparison,
) -> str:
    settled, open_qs = [], []

    for c in comparison.cells:
        if c.kind == "match":
            settled.append(f"  vs {c.opponent}: plays {c.actual} — matches the description (CERTIFIED)")
        elif c.kind == "mismatch":
            settled.append(
                f"  vs {c.opponent}: plays {c.actual}, description implies {c.expected} "
                f"— MISMATCH already established (CERTIFIED)"
            )
        elif c.kind == "uncertified":
            cell = profile.cell(c.opponent)
            ladder = ""
            if cell and cell.by_budget:
                ladder = "; per-budget: " + ", ".join(
                    f"k={k}: {v or 'no verdict'}" for k, v in sorted(cell.by_budget.items())
                )
            open_qs.append(
                f"  vs {c.opponent}: the description implies {c.expected} "
                f"({c.expected_confidence}), but the evaluator did not certify a stable "
                f"answer. {c.detail}{ladder}"
            )
        elif c.kind == "unspecified":
            cell = profile.cell(c.opponent)
            actual = cell.describe() if cell else "not evaluated"
            open_qs.append(
                f"  vs {c.opponent}: the description does not settle this cell. "
                f"The implementation does: {actual}. Is that consistent with the "
                "described strategy?"
            )

    for claim in expectation.structural_claims:
        open_qs.append(f"  structural claim to verify against the term: {claim}")

    return f"""\
# Bot under review: {bot_name}

## Natural-language description (the specification)

{strategy_description.strip()}

## Generated Lean implementation

```lean
{lean_source.strip()}
```

## Already settled by the certified evaluator — do NOT re-litigate

{chr(10).join(settled) if settled else "  (nothing certified)"}

## OPEN questions — your scope

{chr(10).join(open_qs) if open_qs else "  (none)"}

Resolve the open questions against the Lean term above. Cite the sub-terms that
settle them. Return `underdetermined` for anything the term does not decide.
"""


def judge_residual(
    bot_name: str,
    strategy_description: str,
    lean_source: str,
    expectation: Expectation,
    profile: BotProfile,
    comparison: ReviewComparison,
    *,
    model: str = settings.DEFAULT_MODEL,
    max_turns: int = 8,
    max_tokens: int = 16_000,
    thinking_effort: str = settings.DEFAULT_THINKING_EFFORT,
) -> JudgeReview:
    """Adjudicate what Tier A could not decide. ADVISORY — see the module docstring.

    Unlike Tier A1's extractor, the judge DOES see the Lean source: its questions
    are exactly the ones behavior could not answer. That is also why its output is
    weaker evidence and must never gate acceptance on its own.
    """
    handler = ToolHandler()
    captured: dict[str, Any] = {}

    def submit_review(**payload: Any) -> EpisodeStop:
        captured.update(payload)
        return EpisodeStop(
            payload=payload,
            confirmation_text="Review recorded.",
            end_reason="review",
        )

    handler.register_fn("submit_review", submit_review)
    # Unfiltered reads: the judge is SUPPOSED to see the bot under review and the
    # zoo it should be compared against. There is no answer to leak — Tier A2
    # already computed the behavior by machine proof.
    handler.register_fn("read_library_file", _read_library_file)

    def _search(pattern: str) -> str:
        from pd_runner.llm.library_search import format_matches, search_declarations

        return format_matches(search_declarations(pattern), pattern)

    handler.register_fn("search_library", _search)

    client = make_llm_client(
        system_prompt=_SYSTEM_PROMPT,
        tools=[_SUBMIT_TOOL, _READ_LIBRARY_FILE_TOOL, _SEARCH_LIBRARY_TOOL],
        model=model,
        max_iterations=max_turns,
        max_tokens=max_tokens,
        thinking_effort=thinking_effort,
    )

    brief = _residual_brief(
        bot_name, strategy_description, lean_source, expectation, profile, comparison
    )
    _log.log(TRACE, "judge brief:\n%s", brief)

    result = client.run_episode(
        brief, handler, max_turns=max_turns, stop_tool="submit_review"
    )
    payload = result.verdict_input or captured
    if not payload:
        _log.warning("judge submitted no review (end_reason=%s)", result.end_reason)
        return JudgeReview(
            kind="underdetermined",
            unresolved=(f"judge did not return a review ({result.end_reason})",),
        )

    return JudgeReview(
        kind=payload.get("kind", "underdetermined"),
        discrepancies=tuple(
            Discrepancy(
                claim=d.get("claim", ""),
                expected=d.get("expected", ""),
                actual=d.get("actual", ""),
                severity=d.get("severity", "note"),
                evidence=d.get("evidence", ""),
            )
            for d in payload.get("discrepancies") or ()
        ),
        unresolved=tuple(payload.get("unresolved") or ()),
        notes=payload.get("notes", ""),
    )

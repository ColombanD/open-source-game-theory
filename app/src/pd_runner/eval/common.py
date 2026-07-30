"""Shared per-case machinery for the eval harness and the bot-matrix driver.

Both drivers run one matchup through `search_proof_outcome` and record the
same structured result — pass/fail against an expectation, the verdict kind,
real episode/turn/token counters (also on failure), cost, and cache hit rate.
"""

from __future__ import annotations

import re
import time
from dataclasses import dataclass

from pd_runner.config import load_paths
from pd_runner.services.proof_service import search_proof_outcome
from pd_runner.services.verdicts import ProofOutcome, ProofRequest


@dataclass
class CaseRecord:
    left_bot: str
    right_bot: str
    kind: str                     # ProofOutcome.kind (proved/open_*/exhausted/error)
    passed: bool
    expected: str                 # human-readable expectation
    left_action: str | None
    right_action: str | None
    chosen_fuel: int | None
    episodes_used: int
    turns_used: int
    tool_calls_used: int
    input_tokens: int
    output_tokens: int
    cache_read_tokens: int
    cache_creation_tokens: int
    cache_hit_rate: float
    cost_usd: float | None
    elapsed_seconds: float
    model: str = ""
    tier_a: int | None = None
    tier_b: int | None = None
    error: str | None = None
    notebook: str | None = None
    lean_source: str | None = None


def run_case(
    request: ProofRequest,
    *,
    expected_outcome: tuple[str | None, str | None] | None = None,
    expected_verdict: str | None = None,
) -> CaseRecord:
    """Run one matchup and judge it against the expectation.

    - `expected_verdict` set: passes iff the agent's verdict kind matches
      (e.g. a known-OPEN bistable case passes only on `open_bistable` —
      "proving" it or giving up both fail).
    - `expected_outcome` set: passes iff proved with exactly that action pair.
    - neither: passes iff proved (discover mode — the matrix driver).
    """
    t0 = time.monotonic()
    outcome = search_proof_outcome(request)
    elapsed = time.monotonic() - t0

    if expected_verdict is not None:
        passed = outcome.kind == expected_verdict
        expected = f"verdict:{expected_verdict}"
    elif expected_outcome is not None:
        passed = outcome.proved and (
            (outcome.left_action, outcome.right_action) == expected_outcome
        )
        expected = f"({expected_outcome[0]},{expected_outcome[1]})"
    else:
        passed = outcome.proved
        expected = "any-proof"

    return record_from_outcome(
        outcome, passed=passed, expected=expected, elapsed=elapsed, model=request.model
    )


def record_from_outcome(
    outcome: ProofOutcome, *, passed: bool, expected: str, elapsed: float, model: str
) -> CaseRecord:
    usage = outcome.usage
    return CaseRecord(
        left_bot=outcome.left_bot,
        right_bot=outcome.right_bot,
        kind=outcome.kind,
        passed=passed,
        expected=expected,
        left_action=outcome.left_action,
        right_action=outcome.right_action,
        chosen_fuel=extract_chosen_fuel(outcome.lean_source or ""),
        episodes_used=outcome.episodes_used,
        turns_used=outcome.turns_used,
        tool_calls_used=outcome.tool_calls_used,
        input_tokens=usage.input_tokens,
        output_tokens=usage.output_tokens,
        cache_read_tokens=usage.cache_read_tokens,
        cache_creation_tokens=usage.cache_creation_tokens,
        cache_hit_rate=round(usage.cache_hit_rate(), 4),
        cost_usd=usage.cost_usd(model),
        elapsed_seconds=elapsed,
        model=model,
        error=None if passed else outcome.explanation[:500] or None,
        notebook=outcome.notebook or None,
        lean_source=outcome.lean_source,
    )


_FUEL_RE = re.compile(r"outcome\s*\(\s*n\s*\+\s*(\d+)\s*\)")


def extract_chosen_fuel(lean_source: str) -> int | None:
    m = _FUEL_RE.search(lean_source)
    return int(m.group(1)) if m else None


def classify_tier(bot: str) -> int:
    """Bot difficulty tier from its source: 0 = constant, 1 = reactive
    (sim/ite, no search), 2 = `.search`-using (proof-system/Löb machinery)."""
    paths = load_paths()
    for candidate in (
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / f"{bot}.lean",
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{bot}.lean",
    ):
        if candidate.exists():
            src = candidate.read_text(encoding="utf-8")
            if ".search" in src or "Prog.search" in src:
                return 2
            if ".const" in src and ".sim" not in src and ".ite" not in src:
                return 0
            return 1
    return 1

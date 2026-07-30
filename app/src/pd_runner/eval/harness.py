"""M5: Evaluation harness — re-prove a held-out set of existing theorems.

Run with:
    uv run python -m pd_runner.eval.harness [--model MODEL] [--output results.json]
    uv run python -m pd_runner.eval.harness --dry-run   # no API calls, tests plumbing only

Each case hides the existing proof and asks the agent to re-discover it.
Cases 0–9 are the historical 10 (kept unchanged for continuity); cases 10–13
exercise the hard path: `.search` self-play (Löb threshold), the staggered
cross-bot Löb, the exclusion-census negative side, and a known-OPEN bistable
matchup that passes only on the `open_bistable` verdict (verdict quality).

Reports per case: pass/fail, verdict kind, episodes/turns/tool calls, token
totals, cost, cache hit rate.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict

from pd_runner import settings
from pd_runner.eval.common import CaseRecord, run_case
from pd_runner.logging_config import setup_logging
from pd_runner.services.proof_service import ProofRequest

_DRY_RUN_SOURCE = """\
import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PD
open PD.Bots

namespace PD.Theorems

-- dry-run placeholder (no real proof attempted)
theorem dry_run_placeholder : True := trivial

end PD.Theorems
"""


# ---------------------------------------------------------------------------
# Held-out eval set. Ordered roughly easy → hard.
# `la`/`ra` = expected (and prompted) action pair; `fuel` = known-good fuel
# offset (None → the agent picks / threshold form); `verdict` = expected
# verdict kind for non-provable cases (actions are then NOT given).
# ---------------------------------------------------------------------------

EVAL_CASES: list[dict] = [
    # Tier 1: trivial bots (.const action)
    {"left": "CooperateBot", "right": "CooperateBot", "la": "C", "ra": "C", "fuel": 1},
    {"left": "CooperateBot", "right": "DefectBot",    "la": "C", "ra": "D", "fuel": 1},
    {"left": "DefectBot",    "right": "DefectBot",    "la": "D", "ra": "D", "fuel": 1},
    # Tier 2: one-step simulation bots
    {"left": "MirrorBot",    "right": "CooperateBot", "la": "C", "ra": "C", "fuel": 3},
    {"left": "MirrorBot",    "right": "DefectBot",    "la": "D", "ra": "D", "fuel": 3},
    {"left": "OBot",         "right": "CooperateBot", "la": "C", "ra": "C", "fuel": 5},
    {"left": "DBot",         "right": "CooperateBot", "la": "D", "ra": "C", "fuel": 3},
    # Tier 3: multi-step bots
    {"left": "TitForTatBot", "right": "CooperateBot", "la": "C", "ra": "C", "fuel": 3},
    {"left": "TitForTatBot", "right": "DefectBot",    "la": "D", "ra": "D", "fuel": 3},
    {"left": "EBot",         "right": "CooperateBot", "la": "D", "ra": "C", "fuel": 3},
    # Tier 4: `.search` bots — the proof-system / Löb / exclusion path.
    # Löb self-play, ∃k₂ threshold shape (library: outcome_DupocBot_vs_DupocBot).
    {"left": "DupocBot",     "right": "DupocBot",     "la": "C", "ra": "C", "fuel": None},
    # Staggered cross-bot Löb: PrudentBot (2k+64) vs DupocBot k (library:
    # outcome_PrudentBot_vs_DupocBot). The agent must find the staggering.
    {"left": "PrudentBot",   "right": "DupocBot",     "la": "C", "ra": "C", "fuel": None},
    # Exclusion-census negative side: same-k prudence is self-defeating
    # (library: outcome_PrudentBot_vs_PrudentBot = (D,D)).
    {"left": "PrudentBot",   "right": "PrudentBot",   "la": "D", "ra": "D", "fuel": None},
    # Known-OPEN bistable matchup (two fixed points, neither forced): passes
    # ONLY on the open_bistable verdict — a fake proof or giving up both fail.
    {"left": "JustBot",      "right": "MirrorBot",    "verdict": "open_bistable"},
]


def _dry_run_case(request: ProofRequest, expected: str) -> CaseRecord:
    """Exercises retrieval + prompt building without calling the LLM or Lean."""
    from pd_runner.llm.prompts import build_system_prompt_blocks, proof_request_message
    from pd_runner.llm.retrieval import list_known_outcome_theorems, retrieve_few_shots

    hidden = set(request.guard.hidden_bots)
    few_shots = retrieve_few_shots(request.left_bot, request.right_bot, exclude_bots=hidden)
    known = list_known_outcome_theorems(request.left_bot, request.right_bot, exclude_bots=hidden)
    _ = build_system_prompt_blocks(request.left_bot, request.right_bot, guard=request.guard)
    _ = proof_request_message(
        request.left_bot, request.right_bot,
        request.left_action, request.right_action,
        few_shots, known,
        fuel=request.fuel,
    )
    return CaseRecord(
        left_bot=request.left_bot, right_bot=request.right_bot,
        kind="proved", passed=True, expected=expected,
        left_action=request.left_action, right_action=request.right_action,
        chosen_fuel=request.fuel, episodes_used=0, turns_used=0, tool_calls_used=0,
        input_tokens=0, output_tokens=0, cache_read_tokens=0, cache_creation_tokens=0,
        cache_hit_rate=0.0, cost_usd=0.0, elapsed_seconds=0.0, model=request.model,
        lean_source=_DRY_RUN_SOURCE,
    )


def run_eval(
    max_iterations: int = settings.DEFAULT_MAX_ITERATIONS,
    model: str = settings.DEFAULT_MODEL,
    dry_run: bool = False,
    cases_slice: slice = slice(None),
    max_episodes: int | None = None,
) -> list[CaseRecord]:
    results: list[CaseRecord] = []
    cases = EVAL_CASES[cases_slice]
    for case in cases:
        expected_verdict = case.get("verdict")
        la, ra = case.get("la"), case.get("ra")
        req = ProofRequest(
            left_bot=case["left"],
            right_bot=case["right"],
            # For verdict-expectation cases the agent gets no action hint —
            # discovering that the matchup is OPEN is the task.
            left_action=None if expected_verdict else la,
            right_action=None if expected_verdict else ra,
            fuel=case.get("fuel"),
            max_iterations=max_iterations,
            model=model,
            exclude_bots=frozenset({case["left"], case["right"]}),
            max_episodes=max_episodes,
        )
        label = (
            f"{case['left']} vs {case['right']} -> "
            + (f"verdict:{expected_verdict}" if expected_verdict else f"({la},{ra})")
        )
        print(f"\n{'='*60}")
        print(f"Case: {label}")
        print(f"{'='*60}")

        expected_str = (
            f"verdict:{expected_verdict}" if expected_verdict else f"({la},{ra})"
        )
        if dry_run:
            t0 = time.monotonic()
            record = _dry_run_case(req, expected=expected_str)
            record.elapsed_seconds = time.monotonic() - t0
        else:
            record = run_case(
                req,
                expected_outcome=None if expected_verdict else (la, ra),
                expected_verdict=expected_verdict,
            )
        status = "PASSED" if record.passed else f"FAILED (kind={record.kind})"
        cost = f"${record.cost_usd:.2f}" if record.cost_usd else "-"
        print(
            f"  {status} in {record.episodes_used} episode(s), {record.turns_used} turns, "
            f"{record.tool_calls_used} tool calls, {record.elapsed_seconds:.1f}s, {cost}, "
            f"cache {record.cache_hit_rate:.0%}"
        )
        if not record.passed and record.error:
            print(f"  error: {record.error[:300]}")
        results.append(record)

    return results


def print_summary(results: list[CaseRecord]) -> None:
    passed = sum(1 for r in results if r.passed)
    total = len(results)
    total_time = sum(r.elapsed_seconds for r in results)
    total_cost = sum(r.cost_usd or 0.0 for r in results)
    avg_turns = (
        sum(r.turns_used for r in results if r.passed) / passed if passed else 0
    )

    print(f"\n{'='*60}")
    print(f"SUMMARY: {passed}/{total} passed")
    print(f"Average turns (passing): {avg_turns:.1f}")
    print(f"Total wall time: {total_time:.1f}s  |  total cost: ${total_cost:.2f}")
    print(f"{'='*60}")
    print(f"{'Bot pair':<42} {'Result':<7} {'Kind':<12} {'Ep':>2} {'Turns':>5} {'Cache':>6} {'Time':>7}")
    print(f"{'-'*42} {'-'*7} {'-'*12} {'-'*2} {'-'*5} {'-'*6} {'-'*7}")
    for r in results:
        label = f"{r.left_bot} vs {r.right_bot} {r.expected}"
        status = "PASS" if r.passed else "FAIL"
        print(
            f"{label:<42} {status:<7} {r.kind:<12} {r.episodes_used:>2} "
            f"{r.turns_used:>5} {r.cache_hit_rate:>5.0%} {r.elapsed_seconds:>6.1f}s"
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="Proof-search evaluation harness")
    parser.add_argument("--output", default=None, help="Save results to JSON file")
    parser.add_argument("--max-iterations", type=int, default=settings.DEFAULT_MAX_ITERATIONS,
                        help="Turns per episode")
    parser.add_argument("--max-episodes", type=int, default=None,
                        help="Fresh-context episodes per case (default: settings)")
    parser.add_argument("--model", default=settings.DEFAULT_MODEL, help="Anthropic model ID")
    parser.add_argument("--cases", type=int, nargs="*", metavar="N", help="Case selection: omit for all, one int N for first N, two ints N M for slice N:M (0-indexed)")
    parser.add_argument("--dry-run", action="store_true", help="Skip LLM+Lean calls, test plumbing only")
    parser.add_argument("--log-level", default="WARNING", choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"], help="Logging verbosity: TRACE=full, DEBUG=no prompts, INFO=tool calls only")
    args = parser.parse_args()

    setup_logging(args.log_level)

    if args.dry_run:
        print("DRY RUN — no LLM or Lean calls will be made")
    else:
        print(f"Model: {args.model}  |  Turns/episode: {args.max_iterations}"
              + (f"  |  Episodes: {args.max_episodes}" if args.max_episodes else ""))
    cases = args.cases
    if not cases:
        cases_slice = slice(None)
    elif len(cases) == 1:
        cases_slice = slice(cases[0])
    elif len(cases) == 2:
        cases_slice = slice(cases[0], cases[1])
    else:
        parser.error("--cases takes at most 2 integers")
    results = run_eval(
        max_iterations=args.max_iterations, model=args.model,
        dry_run=args.dry_run, cases_slice=cases_slice,
        max_episodes=args.max_episodes,
    )
    print_summary(results)

    if args.output:
        with open(args.output, "w") as f:
            json.dump([asdict(r) for r in results], f, indent=2)
        print(f"\nResults saved to {args.output}")


if __name__ == "__main__":
    main()

"""M5: Evaluation harness — re-prove a held-out set of existing theorems.

Run with:
    uv run python -m pd_runner.eval.harness [--model MODEL] [--output results.json]
    uv run python -m pd_runner.eval.harness --dry-run   # no API calls, tests plumbing only

Each case hides the existing proof and asks the agent to re-discover it.
Reports: per-case pass/fail, iterations used, and a summary table.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from typing import Any
from unittest.mock import patch

from pd_runner.services.proof_service import ProofRequest, ProofResult, ProofSearchError, search_proof

_DRY_RUN_SOURCE = """\
import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PDNew
open PDNew.Bots

namespace PDNew.Theorems

-- dry-run placeholder (no real proof attempted)
theorem dry_run_placeholder : True := trivial

end PDNew.Theorems
"""


# ---------------------------------------------------------------------------
# Held-out eval set — 10 theorems across difficulty tiers.
# Ordered roughly easy → hard.
# ---------------------------------------------------------------------------

EVAL_CASES: list[dict[str, str]] = [
    # Tier 1: trivial bots (.const action)
    {"left": "CooperateBot", "right": "CooperateBot", "la": "C", "ra": "C"},
    {"left": "CooperateBot", "right": "DefectBot",    "la": "C", "ra": "D"},
    {"left": "DefectBot",    "right": "DefectBot",    "la": "D", "ra": "D"},
    # Tier 2: one-step simulation bots
    {"left": "MirrorBot",    "right": "CooperateBot", "la": "C", "ra": "C"},
    {"left": "MirrorBot",    "right": "DefectBot",    "la": "D", "ra": "D"},
    {"left": "OBot",         "right": "CooperateBot", "la": "C", "ra": "C"},
    {"left": "DBot",         "right": "CooperateBot", "la": "D", "ra": "C"},
    # Tier 3: multi-step / proof-search bots
    {"left": "TitForTatBot", "right": "CooperateBot", "la": "C", "ra": "C"},
    {"left": "TitForTatBot", "right": "DefectBot",    "la": "D", "ra": "D"},
    {"left": "EBot",         "right": "CooperateBot", "la": "D", "ra": "C"},
]


@dataclass
class CaseResult:
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str
    passed: bool
    iterations_used: int
    elapsed_seconds: float
    error: str | None = None
    lean_source: str | None = None


def _dry_run_search_proof(request: ProofRequest) -> ProofResult:
    """Exercises retrieval + prompt building without calling the LLM or Lean."""
    from pd_runner.llm.prompts import build_system_prompt, proof_request_message
    from pd_runner.llm.retrieval import list_known_outcome_theorems, retrieve_few_shots

    few_shots = retrieve_few_shots(request.left_bot, request.right_bot)
    known = list_known_outcome_theorems(request.left_bot, request.right_bot)
    _ = build_system_prompt(request.left_bot, request.right_bot)
    _ = proof_request_message(
        request.left_bot, request.right_bot,
        request.left_action, request.right_action,
        few_shots, known,
    )
    return ProofResult(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=request.left_action,
        right_action=request.right_action,
        lean_source=_DRY_RUN_SOURCE,
        iterations_used=0,
    )


def run_eval(max_iterations: int = 20, model: str = "claude-opus-4-7", dry_run: bool = False) -> list[CaseResult]:
    results: list[CaseResult] = []
    for case in EVAL_CASES:
        req = ProofRequest(
            left_bot=case["left"],
            right_bot=case["right"],
            left_action=case["la"],
            right_action=case["ra"],
            max_iterations=max_iterations,
            model=model,
        )
        label = f"{case['left']} vs {case['right']} -> ({case['la']},{case['ra']})"
        print(f"\n{'='*60}")
        print(f"Case: {label}")
        print(f"{'='*60}")

        t0 = time.monotonic()
        try:
            result = _dry_run_search_proof(req) if dry_run else search_proof(req)
            elapsed = time.monotonic() - t0
            print(f"  PASSED in {result.iterations_used} tool calls, {elapsed:.1f}s")
            results.append(CaseResult(
                left_bot=case["left"],
                right_bot=case["right"],
                left_action=case["la"],
                right_action=case["ra"],
                passed=True,
                iterations_used=result.iterations_used,
                elapsed_seconds=elapsed,
                lean_source=result.lean_source,
            ))
        except (ProofSearchError, RuntimeError) as exc:
            elapsed = time.monotonic() - t0
            print(f"  FAILED after {elapsed:.1f}s: {exc}")
            results.append(CaseResult(
                left_bot=case["left"],
                right_bot=case["right"],
                left_action=case["la"],
                right_action=case["ra"],
                passed=False,
                iterations_used=0,
                elapsed_seconds=elapsed,
                error=str(exc),
            ))

    return results


def print_summary(results: list[CaseResult]) -> None:
    passed = sum(1 for r in results if r.passed)
    total = len(results)
    total_time = sum(r.elapsed_seconds for r in results)
    avg_iters = (
        sum(r.iterations_used for r in results if r.passed) / passed
        if passed else 0
    )

    print(f"\n{'='*60}")
    print(f"SUMMARY: {passed}/{total} passed")
    print(f"Average iterations (passing): {avg_iters:.1f}")
    print(f"Total wall time: {total_time:.1f}s")
    print(f"{'='*60}")
    print(f"{'Bot pair':<45} {'Result':<8} {'Iters':>5} {'Time':>7}")
    print(f"{'-'*45} {'-'*8} {'-'*5} {'-'*7}")
    for r in results:
        label = f"{r.left_bot} vs {r.right_bot} ({r.left_action},{r.right_action})"
        status = "PASS" if r.passed else "FAIL"
        iters = str(r.iterations_used) if r.passed else "-"
        print(f"{label:<45} {status:<8} {iters:>5} {r.elapsed_seconds:>6.1f}s")


def main() -> None:
    parser = argparse.ArgumentParser(description="Proof-search evaluation harness")
    parser.add_argument("--output", default=None, help="Save results to JSON file")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--model", default="claude-opus-4-7", help="Anthropic model ID")
    parser.add_argument("--dry-run", action="store_true", help="Skip LLM+Lean calls, test plumbing only")
    args = parser.parse_args()

    if args.dry_run:
        print("DRY RUN — no LLM or Lean calls will be made")
    else:
        print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")
    results = run_eval(max_iterations=args.max_iterations, model=args.model, dry_run=args.dry_run)
    print_summary(results)

    if args.output:
        data: list[dict[str, Any]] = [asdict(r) for r in results]
        with open(args.output, "w") as f:
            json.dump(data, f, indent=2)
        print(f"\nResults saved to {args.output}")


if __name__ == "__main__":
    main()

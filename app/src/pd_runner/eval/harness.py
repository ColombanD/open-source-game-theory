"""M5: Evaluation harness — re-prove a held-out set of existing theorems.

Run with:
    uv run python -m pd_runner.eval.harness [--output results.json]

Each case hides the existing proof and asks the agent to re-discover it.
Reports: per-case pass/fail, iterations used, and a summary table.
"""

from __future__ import annotations

import argparse
import json
import time
from dataclasses import asdict, dataclass
from typing import Any

from pd_runner.services.proof_service import ProofRequest, ProofSearchError, search_proof


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


def run_eval(max_iterations: int = 20, model: str = "claude-opus-4-7") -> list[CaseResult]:
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
            result = search_proof(req)
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
    args = parser.parse_args()

    print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")
    results = run_eval(max_iterations=args.max_iterations, model=args.model)
    print_summary(results)

    if args.output:
        data: list[dict[str, Any]] = [asdict(r) for r in results]
        with open(args.output, "w") as f:
            json.dump(data, f, indent=2)
        print(f"\nResults saved to {args.output}")


if __name__ == "__main__":
    main()

"""End-to-end pipeline: proof search → library write for DefectBot vs DefectBot.

Run with:
    uv run python -m pd_runner.eval.run_pipeline
    uv run python -m pd_runner.eval.run_pipeline --model claude-sonnet-4-6 --log-level INFO
"""

from __future__ import annotations

import argparse

from pd_runner.logging_config import setup_logging
from pd_runner.services.library_writer import write_proof_to_library
from pd_runner.services.proof_service import ProofRequest, ProofSearchError, search_proof


def main() -> None:
    parser = argparse.ArgumentParser(description="Run the full proof pipeline for DefectBot vs DefectBot")
    parser.add_argument("--model", default="claude-opus-4-7", help="Anthropic model ID")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--log-level", default="WARNING", choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"])
    parser.add_argument("--dry-run", action="store_true", help="Skip writing to library")
    args = parser.parse_args()

    setup_logging(args.log_level)

    req = ProofRequest(
        left_bot="DefectBot",
        right_bot="DefectBot",
        left_action="D",
        right_action="D",
        fuel=1,
        model=args.model,
        max_iterations=args.max_iterations,
        exclude_bots=frozenset({"DefectBot"}),
    )

    print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")
    print("Running proof search for DefectBot vs DefectBot...")

    try:
        result = search_proof(req)
        print(f"Proof found in {result.iterations_used} tool calls.")
    except ProofSearchError as exc:
        print(f"Proof search failed: {exc}")
        return

    print("Writing to library...")
    try:
        wr = write_proof_to_library(result, human_accept=False, dry_run=args.dry_run)
        print(f"Written to: {wr.path}")
        print(f"Build OK: {wr.build_ok}")
    except Exception as exc:
        print(f"Library write failed: {exc}")


if __name__ == "__main__":
    main()

"""Phase 3 pipeline: two NL strategies → two Lean bots → outcome proof.

Flow:
  1. Bot writer agent generates Bot A from a NL description. Human accepts or rejects.
  2. Bot writer agent generates Bot B from a NL description. Human accepts or rejects.
  3. Proof agent discovers and proves the outcome of Bot A vs Bot B.
  4. Proof is written to the library.

Run with:
    uv run python -m pd_runner.eval.run_bot_pipeline \\
        --bot-a-name AlwaysCooperate --bot-a-strategy "Always cooperate" \\
        --bot-b-name AlwaysDefect   --bot-b-strategy "Always defect"
"""

from __future__ import annotations

import argparse

from pd_runner.logging_config import setup_logging
from pd_runner.services.bot_service import BotRequest, BotWriteError, search_bot
from pd_runner.services.library_writer import LibraryWriteError, write_bot_to_library, write_proof_to_library
from pd_runner.services.proof_service import ProofRequest, ProofSearchError, search_proof


def _generate_and_accept_bot(name: str, strategy: str, model: str, max_iterations: int) -> bool:
    """Run bot writer and human acceptance gate. Returns True if bot was accepted."""
    print(f"\n--- Generating {name} ---")
    print(f"Strategy: {strategy}")
    print("Running bot writer agent...")

    try:
        bot_result = search_bot(BotRequest(
            bot_name=name,
            strategy_description=strategy,
            model=model,
            max_iterations=max_iterations,
        ))
        print(f"Bot generated in {bot_result.iterations_used} tool calls.")
        print(f"\n--- Generated Lean source ---\n{bot_result.lean_source}\n---")
    except BotWriteError as exc:
        print(f"Bot generation failed: {exc}")
        return False

    try:
        wr = write_bot_to_library(bot_result, human_accept=True, dry_run=False)
        print(f"Bot written to: {wr.path}")
        return True
    except LibraryWriteError as exc:
        print(f"Library write failed: {exc}")
        return False


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate two bots and prove their outcome")
    parser.add_argument("--bot-a-name", required=True, help="Name for bot A")
    parser.add_argument("--bot-a-strategy", required=True, help="NL strategy description for bot A")
    parser.add_argument("--bot-b-name", required=True, help="Name for bot B")
    parser.add_argument("--bot-b-strategy", required=True, help="NL strategy description for bot B")
    parser.add_argument("--model", default="claude-opus-4-7")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--log-level", default="WARNING", choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"])
    args = parser.parse_args()

    setup_logging(args.log_level)
    print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")

    # --- Step 1 & 2: Generate and accept both bots ---
    if not _generate_and_accept_bot(args.bot_a_name, args.bot_a_strategy, args.model, args.max_iterations):
        return
    if not _generate_and_accept_bot(args.bot_b_name, args.bot_b_strategy, args.model, args.max_iterations):
        return

    # --- Step 3: Prove outcome between the two bots ---
    print(f"\n--- Proving outcome: {args.bot_a_name} vs {args.bot_b_name} ---")
    print("Proof agent will discover and prove the outcome...")

    try:
        proof = search_proof(ProofRequest(
            left_bot=args.bot_a_name,
            right_bot=args.bot_b_name,
            model=args.model,
            max_iterations=args.max_iterations,
        ))
        print(f"Proved: ({proof.left_action}, {proof.right_action}) in {proof.iterations_used} iterations")
    except ProofSearchError as exc:
        print(f"Proof failed: {exc}")
        return

    # --- Step 4: Write proof to library ---
    try:
        wr = write_proof_to_library(proof, human_accept=False, dry_run=False)
        print(f"Written: {wr.path}")
    except LibraryWriteError as exc:
        print(f"Library write failed: {exc}")


if __name__ == "__main__":
    main()

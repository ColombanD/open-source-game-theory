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

from pd_runner.config import load_paths
from pd_runner.logging_config import setup_logging
from pd_runner.services.bot_service import BotRequest, BotResult, BotWriteError, search_bot
from pd_runner.services.library_writer import LibraryWriteError, bot_file_path, write_bot_to_library, write_proof_to_library
from pd_runner.services.proof_service import ProofRequest, ProofSearchError, search_proof


def _resolve_bot(name: str, strategy: str, model: str, max_iterations: int) -> tuple[str, BotResult] | None:
    """Handle the case where a bot name may already exist.

    Returns (final_name, BotResult) or None if the user aborted.
    If the bot already exists, asks the user to overwrite / rename / use existing.
    """
    paths = load_paths()
    llm_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations"

    # Check if name is taken before running the agent.
    if (llm_dir / f"{name}.lean").exists():
        existing_source = (llm_dir / f"{name}.lean").read_text(encoding="utf-8")
        print(f"\nBot '{name}' already exists in the library.")
        print(f"\n--- Existing Lean source ---\n{existing_source}---")
        print("  [o] Overwrite with a newly generated bot")
        print("  [r] Rename — generate under a different name")
        print("  [u] Use the existing bot as-is")
        print("  [x] Abort")
        choice = input("Choice [o/r/u/x]: ").strip().lower()

        if choice == "u":
            print(f"Using existing {name}.")
            return name, BotResult(bot_name=name, lean_source=existing_source, iterations_used=0)
        elif choice == "r":
            name = input(f"New name for this bot: ").strip()
            if not name:
                print("Aborted.")
                return None
            # Recurse with the new name (handles the case where that name also exists)
            return _resolve_bot(name, strategy, model, max_iterations)
        elif choice == "o":
            pass  # fall through to generation + overwrite
        else:
            print("Aborted.")
            return None

    # Generate the bot.
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
        return None

    # Human acceptance gate.
    try:
        overwrite = (llm_dir / f"{name}.lean").exists()
        wr = write_bot_to_library(bot_result, human_accept=True, dry_run=False, overwrite=overwrite)
        print(f"Bot written to: {wr.path}")
        return name, bot_result
    except LibraryWriteError as exc:
        print(f"Library write failed: {exc}")
        return None


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

    # --- Step 1 & 2: Resolve both bots (generate or reuse existing) ---
    resolved_a = _resolve_bot(args.bot_a_name, args.bot_a_strategy, args.model, args.max_iterations)
    if resolved_a is None:
        return
    bot_a_name, _ = resolved_a

    resolved_b = _resolve_bot(args.bot_b_name, args.bot_b_strategy, args.model, args.max_iterations)
    if resolved_b is None:
        return
    bot_b_name, _ = resolved_b

    # --- Step 3: Prove outcome between the two bots ---
    print(f"\n--- Proving outcome: {bot_a_name} vs {bot_b_name} ---")
    print("Proof agent will discover and prove the outcome...")

    try:
        proof = search_proof(ProofRequest(
            left_bot=bot_a_name,
            right_bot=bot_b_name,
            model=args.model,
            max_iterations=args.max_iterations,
        ))
        print(f"Proved: ({proof.left_action}, {proof.right_action}) in {proof.iterations_used} iterations")
        print(f"\n--- Lean proof ---\n{proof.lean_source}\n---")
    except ProofSearchError as exc:
        print(f"Proof failed: {exc}")
        return

    # --- Step 4: Human accepts proof, then write to library ---
    answer = input("\nAccept proof and write to library? [y/N] ").strip().lower()
    if answer != "y":
        print("Proof not written.")
        return

    try:
        wr = write_proof_to_library(proof, human_accept=False, dry_run=False)
        print(f"Written: {wr.path}")
    except LibraryWriteError as exc:
        print(f"Library write failed: {exc}")


if __name__ == "__main__":
    main()

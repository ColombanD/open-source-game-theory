"""Generate one or more bots from natural language descriptions and write
them to the Lean library — without running the proof step.

Examples:
    # Single bot
    uv run python -m pd_runner.eval.run_bot_writer \
        --name KindBot --strategy "Always cooperates unless opponent defected last round"

    # Multiple bots in one run (interleaved name/strategy pairs)
    uv run python -m pd_runner.eval.run_bot_writer \
        --name KindBot --strategy "..." \
        --name MeanBot --strategy "..."
"""

from __future__ import annotations

import argparse

from pd_runner.config import load_paths
from pd_runner.logging_config import setup_logging
from pd_runner.services.bot_service import BotRequest, BotResult, BotWriteError, search_bot
from pd_runner.services.library_writer import LibraryWriteError, write_bot_to_library


def _resolve_bot(name: str, strategy: str, model: str, max_iterations: int) -> str | None:
    """Generate one bot (or reuse/rename if name clashes) and write it to the library.

    Returns the final bot name (possibly renamed) on success, or None on abort/failure.
    """
    paths = load_paths()
    llm_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations"

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
            return name
        elif choice == "r":
            name = input("New name for this bot: ").strip()
            if not name:
                print("Aborted.")
                return None
            return _resolve_bot(name, strategy, model, max_iterations)
        elif choice == "o":
            pass
        else:
            print("Aborted.")
            return None

    print(f"\n--- Generating {name} ---")
    print(f"Strategy: {strategy}")
    print("Running bot writer agent...")

    try:
        bot_result: BotResult = search_bot(BotRequest(
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

    try:
        overwrite = (llm_dir / f"{name}.lean").exists()
        wr = write_bot_to_library(bot_result, human_accept=True, dry_run=False, overwrite=overwrite)
        print(f"Bot written to: {wr.path}")
        return name
    except LibraryWriteError as exc:
        print(f"Library write failed: {exc}")
        return None


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Translate natural-language bot descriptions to Lean and add them to the library "
                    "(bot-writer half of the pipeline only — no proofs)."
    )
    parser.add_argument("--name", action="append", required=True,
                        help="Bot name. Repeat for multiple bots (pair each --name with a --strategy in order).")
    parser.add_argument("--strategy", action="append", required=True,
                        help="NL strategy description. Repeat once per --name.")
    parser.add_argument("--model", default="claude-opus-4-7")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--log-level", default="WARNING",
                        choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"])
    args = parser.parse_args()

    if len(args.name) != len(args.strategy):
        parser.error("--name and --strategy must be given the same number of times "
                     f"(got {len(args.name)} names and {len(args.strategy)} strategies)")

    setup_logging(args.log_level)
    print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")
    print(f"Bots to generate: {len(args.name)}")

    written: list[str] = []
    skipped: list[str] = []
    for name, strategy in zip(args.name, args.strategy):
        final = _resolve_bot(name, strategy, args.model, args.max_iterations)
        if final is None:
            skipped.append(name)
        else:
            written.append(final)

    print(f"\n{'='*60}")
    print(f"SUMMARY: {len(written)} bot(s) written, {len(skipped)} skipped/failed")
    if written:
        print(f"  Written: {', '.join(written)}")
    if skipped:
        print(f"  Skipped: {', '.join(skipped)}")
    print(f"{'='*60}")


if __name__ == "__main__":
    main()

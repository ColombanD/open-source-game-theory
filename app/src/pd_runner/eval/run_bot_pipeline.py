"""Phase 3 pipeline: NL strategy description → Lean bot definition.

Run with:
    uv run python -m pd_runner.eval.run_bot_pipeline --bot-name KindBot --strategy "..."
    uv run python -m pd_runner.eval.run_bot_pipeline --bot-name KindBot --strategy "..." --log-level INFO
"""

from __future__ import annotations

import argparse

from pd_runner.logging_config import setup_logging
from pd_runner.services.bot_service import BotRequest, BotWriteError, search_bot


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate a Lean 4 bot from a natural language strategy description")
    parser.add_argument("--bot-name", required=True, help="Name for the generated bot (e.g. KindBot)")
    parser.add_argument("--strategy", required=True, help="Natural language description of the bot's strategy")
    parser.add_argument("--model", default="claude-opus-4-7", help="Anthropic model ID")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--log-level", default="WARNING", choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"])
    args = parser.parse_args()

    setup_logging(args.log_level)

    print(f"Model: {args.model}  |  Max iterations: {args.max_iterations}")
    print(f"Bot name: {args.bot_name}")
    print(f"Strategy: {args.strategy}")
    print("Running bot writer agent...")

    req = BotRequest(
        bot_name=args.bot_name,
        strategy_description=args.strategy,
        model=args.model,
        max_iterations=args.max_iterations,
    )

    try:
        result = search_bot(req)
        print(f"\nBot generated in {result.iterations_used} tool calls.")
        print(f"\n--- Generated Lean source ---\n{result.lean_source}\n---")
    except BotWriteError as exc:
        print(f"\nBot generation failed: {exc}")


if __name__ == "__main__":
    main()

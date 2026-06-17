"""Command-line entry point for the LLM distillation pipeline.

Usage::

    distillation-llm --model anthropic/claude-3.5-sonnet [--n 30]

Requires ``OPENROUTER_API_KEY`` set in a gitignored ``.env`` file at the project
root.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .pipeline import RunConfig, run_pipeline


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="distillation-llm",
        description="Measure an LLM's per-opponent cooperation profile by playing "
        "it against every library bot, then fit it to the convex hull.",
    )
    parser.add_argument("--model", required=True, help="OpenRouter model id.")
    parser.add_argument("--n", type=int, default=30,
                        help="Max queries per bot (Bernoulli sample size). Default: 30.")
    parser.add_argument("--min-n", type=int, default=15,
                        help="Early-stop a bot after this many unanimous valid "
                        "replies (~3/min_n upper bound on the other action at 95%%). "
                        "Set equal to --n to disable early stopping. Default: 15.")
    parser.add_argument("--temperature", type=float, default=1.0,
                        help="Sampling temperature; must be >0 to estimate "
                        "probabilities. Default: 1.0.")
    parser.add_argument("--reasoning-effort", default=None,
                        choices=["minimal", "low", "medium", "high", "xhigh"],
                        help="OpenRouter reasoning effort (OpenAI/Anthropic etc.). "
                        "Default: none -- the reasoning param is omitted, so models "
                        "without reasoning support are unaffected.")
    parser.add_argument("--matrix", type=Path, default=Path("data/payoff_matrix.csv"),
                        help="Path to the payoff matrix CSV.")
    parser.add_argument("--output-root", type=Path, default=Path("runs"),
                        help="Root folder for run outputs. Default: runs.")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    config = RunConfig(
        model=args.model,
        n=args.n,
        min_n=args.min_n,
        temperature=args.temperature,
        reasoning_effort=args.reasoning_effort,
        matrix_path=args.matrix,
        output_root=args.output_root,
    )

    print(f"Running {config.n} queries/bot against model {config.model} ...")
    run_dir = run_pipeline(config)
    print(f"\nRun saved to {run_dir}")
    print((run_dir / "report.txt").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())

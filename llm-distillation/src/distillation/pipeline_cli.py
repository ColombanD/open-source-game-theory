"""Command-line entry point for the LLM distillation pipeline.

Usage::

    distillation-llm --model anthropic/claude-3.5-sonnet [--n 30]

Requires the ``OPENROUTER_API_KEY`` environment variable.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .bots import DEFAULT_BOTS_DIR
from .pipeline import RunConfig, run_pipeline


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="distillation-llm",
        description="Measure an LLM's per-opponent cooperation profile by playing "
        "it against every library bot, then fit it to the convex hull.",
    )
    parser.add_argument("--model", required=True, help="OpenRouter model id.")
    parser.add_argument("--n", type=int, default=30,
                        help="Queries per bot (Bernoulli sample size). Default: 30.")
    parser.add_argument("--temperature", type=float, default=1.0,
                        help="Sampling temperature; must be >0 to estimate "
                        "probabilities. Default: 1.0.")
    parser.add_argument("--matrix", type=Path, default=Path("data/payoff_matrix.csv"),
                        help="Path to the payoff matrix CSV.")
    parser.add_argument("--bots-dir", type=Path, default=DEFAULT_BOTS_DIR,
                        help="Directory of bot .lean source files.")
    parser.add_argument("--output-root", type=Path, default=Path("runs"),
                        help="Root folder for run outputs. Default: runs.")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    config = RunConfig(
        model=args.model,
        n=args.n,
        temperature=args.temperature,
        matrix_path=args.matrix,
        bots_dir=args.bots_dir,
        output_root=args.output_root,
    )

    print(f"Running {config.n} queries/bot against model {config.model} ...")
    run_dir = run_pipeline(config)
    print(f"\nRun saved to {run_dir}")
    print((run_dir / "report.txt").read_text())
    return 0


if __name__ == "__main__":
    sys.exit(main())

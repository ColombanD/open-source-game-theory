"""Command-line entry point.

Usage::

    python -m distillation MATRIX_CSV INPUT_VECTOR [--metric L2 ...]

``INPUT_VECTOR`` may be a file (JSON list, CSV/whitespace floats, or a C/D
string) or an inline value (``"CDCDCCDC"`` or ``"1,0,1,0,1,0,1,1"``).
"""

from __future__ import annotations

import argparse
import sys

from .data import format_reference_matrix, load_input_vector, load_library
from .fitting import FITTERS
from .reporting import format_report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="distillation",
        description="Fit a cooperation profile to the convex hull of reference "
        "bots and report the best fit under multiple distances.",
    )
    parser.add_argument("matrix", help="Path to the payoff matrix CSV.")
    parser.add_argument(
        "input_vector",
        help="Input profile x: a file (JSON/CSV floats or C/D string) or an "
        "inline C/D string / comma-separated floats.",
    )
    parser.add_argument(
        "--metric",
        action="append",
        choices=list(FITTERS),
        help="Restrict to specific distance(s); repeatable. Default: all.",
    )
    parser.add_argument(
        "--no-matrix",
        action="store_true",
        help="Do not print the parsed reference matrix R.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    library = load_library(args.matrix)
    if not args.no_matrix:
        print(f"Parsed {library.n} bots (canonical order): {', '.join(library.bots)}")
        print()
        print("Reference matrix R (rows = bots, cols = opponents; C=1, D=0):")
        print(format_reference_matrix(library))
        print()

    x = load_input_vector(args.input_vector, library.n)

    metrics = args.metric or list(FITTERS)
    results = [FITTERS[m](library.R, x) for m in metrics]

    print(format_report(library, results, x))
    return 0


if __name__ == "__main__":
    sys.exit(main())

from __future__ import annotations

import argparse
import json
import sys

from pd_runner.models import MatchupRequest
from pd_runner.services.matchup_service import run_matchup


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run a Lean-verified open-source PD matchup")
    parser.add_argument("--left", required=True, help="Left bot name, e.g. cooperateBot")
    parser.add_argument("--right", required=True, help="Right bot name, e.g. defectBot")
    parser.add_argument("--json", action="store_true", help="Emit JSON output")
    parser.add_argument("--quiet", action="store_true", help="Emit only the action pair")
    parser.add_argument(
        "--keep-file",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Keep generated Lean file (default: true). Use --no-keep-file to delete it after execution.",
    )
    return parser


def main() -> None:
    parser = _build_parser()
    args = parser.parse_args()

    request = MatchupRequest(left_bot=args.left, right_bot=args.right)
    result = run_matchup(request, keep_file=args.keep_file)

    if args.json:
        print(json.dumps(result.__dict__, indent=2))
        return

    if args.quiet:
        print(f"({result.left_action}, {result.right_action})")
        return

    print(f"left bot:  {result.left_bot}")
    print(f"right bot: {result.right_bot}")
    print(f"actions:   ({result.left_action}, {result.right_action})")
    print(f"lean file: {result.lean_file}")
    print(f"command:   {result.command}")


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # pragma: no cover
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(1)

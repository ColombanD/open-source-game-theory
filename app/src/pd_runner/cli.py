from __future__ import annotations

import argparse
import json
import sys

from pd_runner.models import MatchupRequest
from pd_runner.lean.templates import available_bot_names
from pd_runner.services.matchup_service import run_matchup


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Run a Lean-verified open-source PD matchup")
    parser.add_argument("--left", help="Left bot name, e.g. CooperateBot or CupodBot:3")
    parser.add_argument("--right", help="Right bot name, e.g. DefectBot or CupodBot:?")
    parser.add_argument("--list-bots", action="store_true", help="List available Lean bots and exit")
    parser.add_argument(
        "--claim-left",
        choices=["C", "D"],
        help="Optional claimed left action to check against a Lean outcome theorem.",
    )
    parser.add_argument(
        "--claim-right",
        choices=["C", "D"],
        help="Optional claimed right action to check against a Lean outcome theorem.",
    )
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

    if args.list_bots:
        for name in available_bot_names():
            print(name)
        return

    if args.left is None or args.right is None:
        parser.error("--left and --right are required unless --list-bots is used")

    if (args.claim_left is None) != (args.claim_right is None):
        parser.error("--claim-left and --claim-right must be provided together")

    request = MatchupRequest(
        left_bot=args.left,
        right_bot=args.right,
        claim_left_action=args.claim_left,
        claim_right_action=args.claim_right,
    )
    try:
        result = run_matchup(request, keep_file=args.keep_file)
    except Exception as exc:  # pragma: no cover
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(result.__dict__, indent=2))
        return

    if args.quiet:
        print(f"({result.left_action}, {result.right_action})")
        return

    print(f"left bot:  {result.left_bot}")
    print(f"right bot: {result.right_bot}")
    print(f"actions:   ({result.left_action}, {result.right_action})")
    print(f"proof:     {result.proof_theorem_used or 'none'}")
    if result.result_kind != "concrete":
        print(f"kind:      {result.result_kind}")
        print(f"witness:   {result.witness or 'unknown'}")
    print(f"lean file: {result.lean_file}")
    print(f"command:   {result.command}")


if __name__ == "__main__":
    main()

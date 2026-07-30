"""E1 — Full bot-matrix proof automation.

For every ordered pair of bots in the hand-written library, run the proof agent
with no outcome and no fuel hint and record whether it succeeds. Results are
appended to a JSONL file so --resume can skip already-passing pairs.

Run with:
    uv run python -m pd_runner.eval.run_bot_matrix --output results.jsonl
    uv run python -m pd_runner.eval.run_bot_matrix --bots CooperateBot,DefectBot,MirrorBot
    uv run python -m pd_runner.eval.run_bot_matrix --resume --output results.jsonl
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict
from pathlib import Path

from pd_runner import settings
from pd_runner.config import load_paths
from pd_runner.eval.common import CaseRecord, classify_tier, run_case
from pd_runner.logging_config import setup_logging
from pd_runner.services.proof_service import ProofRequest

_classify_tier = classify_tier  # legacy alias


def _discover_bots(include_llm: bool = False) -> list[str]:
    paths = load_paths()
    bots_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots"
    names = sorted(p.stem for p in bots_dir.glob("*.lean"))
    if include_llm:
        llm_dir = bots_dir / "LlmGenerations"
        if llm_dir.exists():
            names.extend(sorted(p.stem for p in llm_dir.glob("*.lean")))
    return names


def _record_pair(rec: dict) -> tuple[str, str]:
    """The (left, right) key of a JSONL record — accepts both the current
    CaseRecord keys and the legacy MatrixResult keys (bot_a/bot_b)."""
    return (
        rec.get("left_bot") or rec.get("bot_a"),
        rec.get("right_bot") or rec.get("bot_b"),
    )


def _load_completed(output_path: Path) -> set[tuple[str, str]]:
    if not output_path.exists():
        return set()
    completed: set[tuple[str, str]] = set()
    with output_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            if rec.get("passed"):
                completed.add(_record_pair(rec))
    return completed


def _run_pair(
    bot_a: str, bot_b: str, model: str, max_iterations: int, max_tokens: int,
    thinking_effort: str,
) -> CaseRecord:
    req = ProofRequest(
        left_bot=bot_a,
        right_bot=bot_b,
        max_iterations=max_iterations,
        max_tokens=max_tokens,
        thinking_effort=thinking_effort,
        model=model,
        exclude_bots=frozenset({bot_a, bot_b}),
    )
    record = run_case(req)  # discover mode: passes iff proved
    record.tier_a = classify_tier(bot_a)
    record.tier_b = classify_tier(bot_b)
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description="E1 — full bot-matrix proof automation")
    parser.add_argument("--output", default="bot_matrix_results.jsonl",
                        help="JSONL file to append results to")
    parser.add_argument("--bots", default=None,
                        help="Comma-separated subset of bot names (default: all hand-written)")
    parser.add_argument("--pair", default=None,
                        help="Run a single pair, format 'BotA,BotB' (overrides --bots; ignores --ordered/--resume)")
    parser.add_argument("--include-llm", action="store_true",
                        help="Also include bots from Bots/LlmGenerations/")
    parser.add_argument("--model", default=settings.DEFAULT_MODEL)
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--max-tokens", type=int, default=settings.DEFAULT_MAX_TOKENS,
                        help="Max output tokens per API call (default: 32000, Opus 4.7 max: 32000)")
    parser.add_argument("--thinking-effort", default="medium",
                        choices=["low", "medium", "high", "xhigh"],
                        help="Thinking effort level (default: medium)")
    parser.add_argument("--resume", action="store_true",
                        help="Skip pairs that already have a passing result in --output")
    parser.add_argument("--log-level", default="WARNING",
                        choices=["TRACE", "DEBUG", "INFO", "WARNING", "ERROR"])
    parser.add_argument("--dry-run", action="store_true",
                        help="Print the pairs that would run, no API calls")
    parser.add_argument("--ordered", action="store_true",
                        help="Run all N*N ordered pairs (default: N*(N+1)/2 unordered pairs, "
                             "since outcome A B and outcome B A are symmetric)")
    args = parser.parse_args()

    setup_logging(args.log_level)

    if args.pair:
        parts = [b.strip() for b in args.pair.split(",") if b.strip()]
        if len(parts) != 2:
            parser.error("--pair must be exactly two bot names, e.g. 'CupodBot,DupocBot'")
        bots = parts
        pairs = [(parts[0], parts[1])]
        mode = "single pair"
        output_path = Path(args.output).resolve()
        completed = set()
    else:
        if args.bots:
            bots = [b.strip() for b in args.bots.split(",") if b.strip()]
        else:
            bots = _discover_bots(include_llm=args.include_llm)

        output_path = Path(args.output).resolve()
        completed = _load_completed(output_path) if args.resume else set()

        if args.ordered:
            pairs = [(a, b) for a in bots for b in bots]
            mode = "ordered"
        else:
            # Half-matrix: each unordered pair once (a ≤ b in list order). outcome A B
            # and outcome B A are symmetric, so we only need to prove one ordering.
            pairs = [(a, b) for i, a in enumerate(bots) for b in bots[i:]]
        mode = "unordered (half-matrix)"
    remaining = [(a, b) for (a, b) in pairs if (a, b) not in completed]

    print(f"Bots ({len(bots)}): {', '.join(bots)}")
    print(f"Mode: {mode}")
    print(f"Model: {args.model}  |  max_tokens: {args.max_tokens}  |  thinking_effort: {args.thinking_effort}  |  max_iterations: {args.max_iterations}")
    print(f"Pairs total: {len(pairs)}  |  remaining: {len(remaining)}  |  completed: {len(completed)}")
    print(f"Output: {output_path}")
    if args.dry_run:
        for a, b in remaining:
            print(f"  would run: {a} vs {b}  (tier {_classify_tier(a)}x{_classify_tier(b)})")
        return

    output_path.parent.mkdir(parents=True, exist_ok=True)

    # Load existing results into a dict keyed by (left, right) so new runs
    # overwrite old ones rather than appending duplicates.
    latest: dict[tuple[str, str], dict] = {}
    if output_path.exists():
        with output_path.open("r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line:
                    r = json.loads(line)
                    latest[_record_pair(r)] = r

    for i, (a, b) in enumerate(remaining, start=1):
        print(f"\n[{i}/{len(remaining)}] {a} vs {b} (tier {classify_tier(a)}x{classify_tier(b)})")
        res = _run_pair(a, b, args.model, args.max_iterations, args.max_tokens, args.thinking_effort)
        latest[(a, b)] = asdict(res)
        # Rewrite the whole file with deduplicated latest results after each pair.
        with output_path.open("w", encoding="utf-8") as f:
            for record in latest.values():
                f.write(json.dumps(record) + "\n")
        cost = f"${res.cost_usd:.2f}" if res.cost_usd else "-"
        status = "PASS" if res.passed else f"FAIL ({res.kind})"
        print(f"  {status}  outcome=({res.left_action},{res.right_action})  fuel={res.chosen_fuel}  "
              f"episodes={res.episodes_used}  turns={res.turns_used}  cache={res.cache_hit_rate:.0%}  "
              f"{cost}  {res.elapsed_seconds:.1f}s")

    # Summary.
    passed = sum(1 for r in latest.values() if r["passed"])
    print(f"\n{'='*60}\nSUMMARY: {passed}/{len(latest)} passed\n{'='*60}")


if __name__ == "__main__":
    main()

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
import re
import time
from dataclasses import asdict, dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.logging_config import setup_logging
from pd_runner.services.proof_service import (
    ProofRequest, ProofSearchError, search_proof,
)


# Tier classification used for stratified reporting.
# Tier 0: constant bots (.const action, no opponent inspection).
# Tier 1: reactive bots (read history / opponent action, no .search).
# Tier 2: .search-using bots (need Axioms.lean).
_TIER_OVERRIDES: dict[str, int] = {
    "CooperateBot": 0,
    "DefectBot": 0,
    "MirrorBot": 1,
    "TitForTatBot": 1,
    "DBot": 1,
    "EBot": 1,
    "OBot": 1,
    "CupodBot": 2,
    "DupocBot": 2,
}


@dataclass
class MatrixResult:
    bot_a: str
    bot_b: str
    tier_a: int
    tier_b: int
    passed: bool
    left_action: str | None
    right_action: str | None
    chosen_fuel: int | None
    iterations: int
    wall_clock_s: float
    error_class: str | None = None
    error_msg: str | None = None


def _discover_bots(include_llm: bool = False) -> list[str]:
    paths = load_paths()
    bots_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots"
    names = sorted(p.stem for p in bots_dir.glob("*.lean"))
    if include_llm:
        llm_dir = bots_dir / "LlmGenerations"
        if llm_dir.exists():
            names.extend(sorted(p.stem for p in llm_dir.glob("*.lean")))
    return names


def _classify_tier(bot: str) -> int:
    if bot in _TIER_OVERRIDES:
        return _TIER_OVERRIDES[bot]
    # Fallback for LLM-generated bots: read the source and detect .search.
    paths = load_paths()
    for candidate in (
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / f"{bot}.lean",
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{bot}.lean",
    ):
        if candidate.exists():
            src = candidate.read_text(encoding="utf-8")
            if ".search" in src or "Prog.search" in src:
                return 2
            if ".const" in src and ".sim" not in src and ".ite" not in src:
                return 0
            return 1
    return 1


_FUEL_RE = re.compile(r"outcome\s*\(\s*n\s*\+\s*(\d+)\s*\)")


def _extract_chosen_fuel(lean_source: str) -> int | None:
    m = _FUEL_RE.search(lean_source)
    return int(m.group(1)) if m else None


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
                completed.add((rec["bot_a"], rec["bot_b"]))
    return completed


def _run_pair(
    bot_a: str, bot_b: str, model: str, max_iterations: int, max_tokens: int,
) -> MatrixResult:
    tier_a, tier_b = _classify_tier(bot_a), _classify_tier(bot_b)
    req = ProofRequest(
        left_bot=bot_a,
        right_bot=bot_b,
        max_iterations=max_iterations,
        max_tokens=max_tokens,
        model=model,
        exclude_bots=frozenset({bot_a, bot_b}),
    )
    t0 = time.monotonic()
    try:
        proof = search_proof(req)
        elapsed = time.monotonic() - t0
        return MatrixResult(
            bot_a=bot_a, bot_b=bot_b,
            tier_a=tier_a, tier_b=tier_b,
            passed=True,
            left_action=proof.left_action,
            right_action=proof.right_action,
            chosen_fuel=_extract_chosen_fuel(proof.lean_source),
            iterations=proof.iterations_used,
            wall_clock_s=elapsed,
        )
    except (ProofSearchError, RuntimeError) as exc:
        elapsed = time.monotonic() - t0
        iters = getattr(exc, "iterations_used", 0)
        return MatrixResult(
            bot_a=bot_a, bot_b=bot_b,
            tier_a=tier_a, tier_b=tier_b,
            passed=False,
            left_action=None, right_action=None, chosen_fuel=None,
            iterations=iters,
            wall_clock_s=elapsed,
            error_class=type(exc).__name__,
            error_msg=str(exc)[:500],
        )


def main() -> None:
    parser = argparse.ArgumentParser(description="E1 — full bot-matrix proof automation")
    parser.add_argument("--output", default="bot_matrix_results.jsonl",
                        help="JSONL file to append results to")
    parser.add_argument("--bots", default=None,
                        help="Comma-separated subset of bot names (default: all hand-written)")
    parser.add_argument("--include-llm", action="store_true",
                        help="Also include bots from Bots/LlmGenerations/")
    parser.add_argument("--model", default="claude-opus-4-7")
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--max-tokens", type=int, default=16384,
                        help="Max output tokens per API call (default: 16384, Opus 4.7 max: 32000)")
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
    print(f"Model: {args.model}  |  max_tokens: {args.max_tokens}  |  max_iterations: {args.max_iterations}")
    print(f"Pairs total: {len(pairs)}  |  remaining: {len(remaining)}  |  completed: {len(completed)}")
    print(f"Output: {output_path}")
    if args.dry_run:
        for a, b in remaining:
            print(f"  would run: {a} vs {b}  (tier {_classify_tier(a)}x{_classify_tier(b)})")
        return

    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("a", encoding="utf-8") as f:
        for i, (a, b) in enumerate(remaining, start=1):
            print(f"\n[{i}/{len(remaining)}] {a} vs {b} (tier {_classify_tier(a)}x{_classify_tier(b)})")
            res = _run_pair(a, b, args.model, args.max_iterations, args.max_tokens)
            f.write(json.dumps(asdict(res)) + "\n")
            f.flush()
            status = "PASS" if res.passed else f"FAIL ({res.error_class})"
            print(f"  {status}  outcome=({res.left_action},{res.right_action})  fuel={res.chosen_fuel}  "
                  f"iters={res.iterations}  {res.wall_clock_s:.1f}s")

    # Summary.
    all_results = []
    with output_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                all_results.append(json.loads(line))
    passed = sum(1 for r in all_results if r["passed"])
    print(f"\n{'='*60}\nSUMMARY: {passed}/{len(all_results)} passed across all logged runs\n{'='*60}")


if __name__ == "__main__":
    main()

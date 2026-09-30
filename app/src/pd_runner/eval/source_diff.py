"""`python -m pd_runner.eval.source_diff` — the engine-vs-`S'` cell report.

Per zoo (`tau.matrix.ZOOS`, natives read as their base bot, plus the 12 paper base
bots), the unordered pairs that AGREE, FLIP (both values), are FLOORS (with the hinge)
or are MISSING on either side — `eval.outcome_matrix.diff_sources`. Writes a Markdown
report, by default `app/generated/source_diff.md` (a committed artifact, like the
exports it is derived from).

    uv run python -m pd_runner.eval.source_diff
    uv run python -m pd_runner.eval.source_diff --zoo body --output /tmp/body.md
    uv run python -m pd_runner.eval.source_diff --bots DupocBot,DBot,EBot
"""

from __future__ import annotations

import argparse
from pathlib import Path

from pd_runner.eval.outcome_matrix import SourceDiff, diff_sources

DEFAULT_OUTPUT = Path(__file__).resolve().parents[3] / "generated" / "source_diff.md"


def main(argv: list[str] | None = None) -> SourceDiff:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--zoo", default=None,
                        help="restrict the report to one registered zoo (default: all)")
    parser.add_argument("--bots", default=None,
                        help="comma-separated custom roster instead of the zoos")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT,
                        help=f"Markdown report path (default: {DEFAULT_OUTPUT})")
    args = parser.parse_args(argv)

    if args.bots:
        diff = diff_sources(tuple(b.strip() for b in args.bots.split(",") if b.strip()))
    elif args.zoo:
        from pd_runner.tau.matrix import NATIVE_PLAYERS, get_zoo

        zoo = get_zoo(args.zoo)
        base = tuple(dict.fromkeys(
            NATIVE_PLAYERS[b].base if b in NATIVE_PLAYERS else b for b in zoo.bots))
        diff = diff_sources(base)
    else:
        diff = diff_sources()

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(diff.render_markdown(), encoding="utf-8")
    for z in diff.zoos:
        print(f"{z.key:22s} pairs {len(z.pairs):3d}  agree {len(z.agreeing):3d}  "
              f"flip {len(z.flips):2d}  floor {len(z.floors):2d} ({len(z.floor_rows)} rows)  "
              f"missing {len(z.missing):2d}")
    print(f"wrote {args.output}")
    return diff


if __name__ == "__main__":
    main()

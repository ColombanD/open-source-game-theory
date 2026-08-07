"""Method 2 cross-check via lrsnash (lrslib command-line tool).

lrsnash is the canonical Avis-Fukuda reverse-search implementation. We
shell out to it through a temporary input file, parse its output, and
return the same `ExtremeNE` records that the pygambit wrapper produces.

Input format (lrsnash):
    m n
    <blank>
    <row 1 of A>      # m rows × n cols
    ...
    <blank>
    <row 1 of B>      # m rows × n cols
    ...

Output format (one "block" per face of the equilibrium correspondence,
blocks separated by blank lines; comments begin with `*`):
    2 <p2[1]> <p2[2]> ... <p2[n]> <payoff_to_p1>
    ...
    1 <p1[1]> <p1[2]> ... <p1[m]> <payoff_to_p2>
    ...

Within a block, the equilibria are the cross product of the listed
player-2 mixtures with the listed player-1 mixtures.
"""

from __future__ import annotations

import subprocess
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import List, Optional, Tuple

from src.nash.extreme_ne import ExtremeNE, make_extreme_ne


def _format_entry(x: Fraction) -> str:
    """Format a Fraction for lrsnash input."""
    if x.denominator == 1:
        return str(x.numerator)
    return f"{x.numerator}/{x.denominator}"


def _write_input(
    A: List[List[Fraction]],
    B: List[List[Fraction]],
    path: Path,
) -> None:
    m = len(A)
    n = len(A[0]) if m > 0 else 0
    if len(B) != m or any(len(r) != n for r in A) or any(len(r) != n for r in B):
        raise ValueError("A and B must be conforming m×n matrices")
    lines = [f"{m} {n}", ""]
    for row in A:
        lines.append(" ".join(_format_entry(x) for x in row))
    lines.append("")
    for row in B:
        lines.append(" ".join(_format_entry(x) for x in row))
    lines.append("")
    path.write_text("\n".join(lines))


def _parse_fraction(s: str) -> Fraction:
    return Fraction(s)


@dataclass
class _Block:
    p2_strategies: List[List[Fraction]]      # mixtures over column player
    p1_strategies: List[List[Fraction]]      # mixtures over row player


def _parse_output(text: str, m: int, n: int) -> List[_Block]:
    """Return a list of blocks; each block holds the P2 and P1 strategy lists."""
    blocks: List[_Block] = []
    current = _Block(p2_strategies=[], p1_strategies=[])
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            if current.p1_strategies or current.p2_strategies:
                blocks.append(current)
                current = _Block(p2_strategies=[], p1_strategies=[])
            continue
        if line.startswith("*"):
            continue
        tokens = line.split()
        player = tokens[0]
        # Tokens after player tag: a strategy vector followed by an
        # equilibrium-payoff scalar.
        if player == "1":
            if len(tokens) < 2 + m:
                # missing payoff column; older lrsnash sometimes omits it
                strat = [_parse_fraction(t) for t in tokens[1 : 1 + m]]
            else:
                strat = [_parse_fraction(t) for t in tokens[1 : 1 + m]]
            current.p1_strategies.append(strat)
        elif player == "2":
            strat = [_parse_fraction(t) for t in tokens[1 : 1 + n]]
            current.p2_strategies.append(strat)
        # Anything else (e.g. spurious comments without `*`) is ignored
    if current.p1_strategies or current.p2_strategies:
        blocks.append(current)
    return blocks


def enumerate_lrsnash(
    A_shifted: List[List[Fraction]],
    B_shifted: List[List[Fraction]],
    lrsnash_bin: str = "lrsnash",
    timeout_seconds: int = 300,
) -> List[ExtremeNE]:
    """Return all extreme NE of (A_shifted, B_shifted) via lrsnash."""
    m = len(A_shifted)
    n = len(A_shifted[0]) if m > 0 else 0

    with tempfile.TemporaryDirectory() as td:
        in_path = Path(td) / "game.nash"
        _write_input(A_shifted, B_shifted, in_path)
        proc = subprocess.run(
            [lrsnash_bin, str(in_path)],
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"lrsnash failed (returncode={proc.returncode}):\n"
                f"stdout: {proc.stdout}\nstderr: {proc.stderr}"
            )
        text = proc.stdout

    blocks = _parse_output(text, m=m, n=n)

    out: List[ExtremeNE] = []
    raw_idx = 0
    for block_id, block in enumerate(blocks):
        if not block.p1_strategies or not block.p2_strategies:
            continue
        for xi in block.p1_strategies:
            for eta in block.p2_strategies:
                # Sanity: probabilities sum to 1
                if sum(xi) != Fraction(1) or sum(eta) != Fraction(1):
                    raise ValueError(
                        f"lrsnash block {block_id}: probabilities do not sum to 1 "
                        f"(xi sum={sum(xi)}, eta sum={sum(eta)})"
                    )
                out.append(
                    make_extreme_ne(
                        xi=tuple(xi),
                        eta=tuple(eta),
                        finder="lrsnash",
                        raw_index=raw_idx,
                        label_set_size=None,
                        component_id=block_id,
                    )
                )
                raw_idx += 1
    return out


def lrsnash_version(lrsnash_bin: str = "lrsnash") -> str:
    """Best-effort: extract the lrsnash banner version, or 'unknown' on failure.

    lrsnash has no `--version` flag; it prints its banner only when processing
    an input file. We feed it a minimal valid game and parse the banner.
    """
    try:
        with tempfile.TemporaryDirectory() as td:
            in_path = Path(td) / "probe.nash"
            in_path.write_text("1 1\n\n1\n\n1\n")
            proc = subprocess.run(
                [lrsnash_bin, str(in_path)],
                capture_output=True,
                text=True,
                timeout=10,
            )
            for line in proc.stdout.splitlines():
                stripped = line.strip()
                if stripped.startswith("*lrsnash"):
                    return stripped.lstrip("*").strip()
    except Exception:
        pass
    return "unknown"

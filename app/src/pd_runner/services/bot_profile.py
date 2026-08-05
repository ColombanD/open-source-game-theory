"""Tier A2 of the bot reviewer: the CERTIFIED behavioral profile of a bot.

What a bot *does* against the canonical opponents, computed with the engine's
certified evaluator (`outcomeG (guardFastN …)`) and no LLM whatsoever. Every
`stable`/`phase_dependent` cell here is machine-certified equal to the classical
`outcome` via `outcomeG_sound ∘ guardFast_sound` — this is ground truth, not an
opinion about source code, which is precisely why it is the primary gate and the
LLM judge is only the fallback (see BOT_REVIEWER_SPEC.md §2).

THE BUDGET SWEEP IS NOT OPTIONAL. A bot's outcome is genuinely k-dependent:
`WaryBot vs DefectBot` is `(C, D)` at k=2,4 and `(D, D)` at k=16 — the budget
phase transition. A reviewer that sampled a single k would report that budget
artifact as a faithfulness failure ("you said it defects against defectors, but
it cooperates"). So we sweep, and `phase_dependent` is a first-class cell verdict
that is NEVER a mismatch on its own — "cooperates until it can prove things, then
defects" is often exactly what the natural-language description meant.

Cost is ~3-8s per cell and flat in k (measured), so the sweep is cheap: four
opponents × four budgets ≈ 25s per bot at 2 workers.

MEMORY DISCIPLINE (learned the hard way — 2026-08-05, third machine OOM in this
project's history). A `decFull` hop sweep can balloon to many GB in seconds, so
every cell runs under `lean -M`. The per-cell cap is NOT the safety property:
`jobs × memory_mb` is what the machine actually sees. `PROFILE_MEMORY_MB` and
`MAX_TOTAL_MEMORY_MB` below keep that product bounded, and `build_profile`
clamps `jobs` to satisfy it rather than trusting the caller. Do NOT run several
profile sweeps concurrently — each clamps only its OWN footprint.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator
from dataclasses import dataclass, field
from pathlib import Path
from typing import Literal

from pd_runner.config import load_paths
from pd_runner.eval.outcome_prepass import (
    REGISTRY,
    BotSpec,
    CellResult,
    bot_spec_from_source,
    run_cells,
)
from pd_runner.logging_config import get_logger

_log = get_logger("services.bot_profile")

# The four canonical opponents (CLAUDE.md Phase 3 / Phase 4 E2b). All four are
# search-free (`guard is None`), so no cell is a both-searcher cell and the
# expensive `--force-hard` regime is structurally out of scope here.
CANONICAL_OPPONENTS: tuple[str, ...] = (
    "CooperateBot",
    "DefectBot",
    "MirrorBot",
    "TitForTatBot",
)

# Spread across the regimes where transitions were observed: 2 and 4 are the
# calibrated cheap points, 6 sits between them and 16, and 16 is where WaryBot's
# (C,D) → (D,D) transition has already landed. 32 is excluded — it OOMs on
# several cells for reasons unrelated to k (memory is not monotone in k).
DEFAULT_BUDGETS: tuple[int, ...] = (2, 4, 6, 16)

# Memory budget. The per-cell cap bounds ONE lean process; the machine sees
# `jobs × memory_mb`, so both matter.
#
# 3072MB is MEASURED, not chosen for comfort: WaryBot-vs-CooperateBot at k=2 is
# `determined` at 3072 and dies with a memory_exception at 2560. Lowering this
# does not make the sweep safer — it silently turns determined cells into
# `undetermined`, which is worse than an OOM because it looks like a real Löb
# boundary. If memory pressure is the problem, cut `jobs`, not this.
PROFILE_MEMORY_MB = 3072
# Two concurrent cells at the measured cap. Raising this is what took the
# machine down on 2026-08-05 (two sweeps x 4 workers x 3GB).
MAX_TOTAL_MEMORY_MB = 6144
DEFAULT_JOBS = 2

# Per-cell wall clock. Cells that have not committed by here are effectively
# infeasible (measured: determined cells land in 3-8s), and letting them run
# only holds memory longer.
DEFAULT_TIMEOUT = 90

CellVerdict = Literal["stable", "phase_dependent", "undetermined"]


@dataclass(frozen=True)
class ProfileCell:
    """What the bot plays against one opponent, across the budget sweep."""

    opponent: str
    verdict: CellVerdict
    my_action: str | None          # "C"/"D" when stable; None otherwise
    opponent_action: str | None
    by_budget: dict[int, str | None] = field(default_factory=dict)  # k -> "(C, D)" or None
    note: str = ""

    @property
    def transition_budgets(self) -> list[int]:
        """Budgets at which the outcome differs from the lowest determined one."""
        determined = {k: v for k, v in sorted(self.by_budget.items()) if v is not None}
        if len(determined) < 2:
            return []
        first = next(iter(determined.values()))
        return [k for k, v in determined.items() if v != first]

    def describe(self) -> str:
        if self.verdict == "stable":
            return f"{self.my_action} (vs {self.opponent_action}) at all determined budgets"
        if self.verdict == "phase_dependent":
            ladder = ", ".join(
                f"k={k}: {v or '?'}" for k, v in sorted(self.by_budget.items())
            )
            return f"budget-dependent — {ladder}"
        return f"undetermined ({self.note})"


@dataclass(frozen=True)
class BotProfile:
    """A bot's certified behavior against the canonical opponents."""

    bot_name: str
    cells: tuple[ProfileCell, ...]
    budgets: tuple[int, ...]
    raw: tuple[CellResult, ...] = ()

    def cell(self, opponent: str) -> ProfileCell | None:
        return next((c for c in self.cells if c.opponent == opponent), None)

    @property
    def determined_cells(self) -> tuple[ProfileCell, ...]:
        return tuple(c for c in self.cells if c.verdict != "undetermined")

    @property
    def coverage(self) -> float:
        """Fraction of opponents on which the certified evaluator committed."""
        return len(self.determined_cells) / len(self.cells) if self.cells else 0.0

    def actions_by_opponent(self) -> dict[str, str | None]:
        """`{opponent: "C"/"D"}` for stable cells; None where not stable."""
        return {c.opponent: c.my_action for c in self.cells}

    def behavior_key(self) -> tuple[tuple[str, str, str | None], ...]:
        """Timing-free projection for comparing two profiles BEHAVIORALLY.

        Do NOT use `profile_a == profile_b` for that: `raw` holds `CellResult`s
        carrying per-cell wall-clock `seconds`, so two runs with identical
        behavior compare UNEQUAL. Any "did the behavior change?" check written
        against `==` silently never fires — which is exactly what the rewriter
        loop's stop-early guard needs (see docs/BOT_REVIEWER.md §7).
        """
        return tuple((c.opponent, c.verdict, c.my_action) for c in self.cells)

    def render(self) -> str:
        width = max((len(c.opponent) for c in self.cells), default=10) + 2
        lines = [
            f"Certified behavioral profile — {self.bot_name} "
            f"(budgets {', '.join(str(k) for k in self.budgets)})"
        ]
        for c in self.cells:
            lines.append(f"  vs {c.opponent:<{width}} {c.describe()}")
        lines.append(
            f"  coverage: {len(self.determined_cells)}/{len(self.cells)} opponents certified"
        )
        return "\n".join(lines)


def _classify(opponent: str, results: list[CellResult]) -> ProfileCell:
    """Collapse one opponent's budget ladder into a single cell verdict."""
    by_budget: dict[int, str | None] = {
        r.budget: (r.outcome if r.status == "determined" else None) for r in results
    }
    determined = [r for r in results if r.status == "determined" and r.outcome]

    if not determined:
        notes = {r.note for r in results if r.note}
        statuses = sorted({r.status for r in results})
        return ProfileCell(
            opponent=opponent,
            verdict="undetermined",
            my_action=None,
            opponent_action=None,
            by_budget=by_budget,
            note="; ".join(sorted(notes)) or f"no verdict ({', '.join(statuses)})",
        )

    outcomes = {r.outcome for r in determined}
    if len(outcomes) > 1:
        lowest = min(determined, key=lambda r: r.budget)
        highest = max(determined, key=lambda r: r.budget)
        return ProfileCell(
            opponent=opponent,
            verdict="phase_dependent",
            my_action=None,
            opponent_action=None,
            by_budget=by_budget,
            note=(
                f"budget phase transition: {lowest.outcome} at k={lowest.budget} → "
                f"{highest.outcome} at k={highest.budget}"
            ),
        )

    mine, theirs = next(iter(outcomes)).strip("()").split(", ")
    return ProfileCell(
        opponent=opponent,
        verdict="stable",
        my_action=mine,
        opponent_action=theirs,
        by_budget=by_budget,
        note=f"certified at k ∈ {{{', '.join(str(r.budget) for r in sorted(determined, key=lambda x: x.budget))}}}",
    )


@contextlib.contextmanager
def staged_bot(
    bot_name: str, lean_source: str, *, engine_dir: Path | None = None
) -> Iterator[str]:
    """Temporarily place a not-yet-accepted bot where Lean can import it.

    The profile has to run BEFORE the human acceptance gate — that is the whole
    point of showing it at the gate — but `outcomeG` needs a real importable
    module. So stage the source at its canonical path, yield the module name,
    and remove it afterwards. Same shape as `llm.tools._run_lean_build`, which
    already compiles candidate bots this way.

    Refuses to touch a path that already exists: an accepted library bot must
    never be clobbered (and, on exit, deleted) by a profiling run.
    """
    engine = engine_dir if engine_dir is not None else load_paths().lean_engine_dir
    target = (
        engine / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{bot_name}.lean"
    )
    if target.exists():
        raise FileExistsError(
            f"{target} already exists — profile it by name instead of staging, "
            "so an accepted bot is not overwritten"
        )
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(lean_source.rstrip("\n") + "\n", encoding="utf-8")
    _log.info("staged %s at %s for profiling", bot_name, target)
    try:
        yield f"PrisonersDilemma.Bots.LlmGenerations.{bot_name}"
    finally:
        target.unlink(missing_ok=True)
        # Drop build artifacts too: a stale .olean for a bot whose source is
        # gone would let a later import silently succeed against dead code.
        # Layout (verified): .lake/build/lib/lean/<mod path>.{olean,ilean,trace,*.hash}
        # and .lake/build/ir/<mod path>.{c,c.hash,setup.json}.
        rel = Path("PrisonersDilemma") / "Bots" / "LlmGenerations"
        for base in (
            engine / ".lake" / "build" / "lib" / "lean" / rel,
            engine / ".lake" / "build" / "ir" / rel,
        ):
            for stale in base.glob(f"{bot_name}.*"):
                stale.unlink(missing_ok=True)
        _log.info("unstaged %s", bot_name)


def build_profile(
    bot_name: str,
    *,
    lean_source: str | None = None,
    module: str | None = None,
    opponents: tuple[str, ...] = CANONICAL_OPPONENTS,
    budgets: tuple[int, ...] = DEFAULT_BUDGETS,
    engine_dir: Path | None = None,
    jobs: int = DEFAULT_JOBS,
    timeout: int = DEFAULT_TIMEOUT,
    memory_mb: int = PROFILE_MEMORY_MB,
    progress=None,
) -> BotProfile:
    """Compute `bot_name`'s certified profile against `opponents`.

    For a bot already in the prepass REGISTRY, name alone suffices. For a
    freshly generated bot, pass `lean_source` (and `module`, defaulting to the
    LlmGenerations path) — its spec is DERIVED from that source rather than
    guessed, so a two-budget bot cannot be silently applied to one argument.

    `jobs` is CLAMPED so `jobs × memory_mb ≤ MAX_TOTAL_MEMORY_MB`: a caller
    asking for more parallelism than the memory ceiling allows gets fewer
    workers, not an OOM. Concurrent `build_profile` calls each clamp only
    themselves — run them sequentially.
    """
    engine = engine_dir if engine_dir is not None else load_paths().lean_engine_dir
    registry: dict[str, BotSpec] = dict(REGISTRY)

    if lean_source is not None:
        mod = module or f"PrisonersDilemma.Bots.LlmGenerations.{bot_name}"
        registry[bot_name] = bot_spec_from_source(bot_name, mod, lean_source)
        _log.info("derived spec for %s: %s", bot_name, registry[bot_name])
    elif bot_name not in registry:
        raise ValueError(
            f"{bot_name!r} is not in the prepass registry; pass lean_source= to "
            "derive its spec from the generated file"
        )

    unknown = [o for o in opponents if o not in registry]
    if unknown:
        raise ValueError(f"unknown opponent(s): {', '.join(unknown)}")

    safe_jobs = max(1, min(jobs, MAX_TOTAL_MEMORY_MB // max(memory_mb, 1)))
    if safe_jobs != jobs:
        _log.warning(
            "clamping jobs %d -> %d: %d workers x %dMB would exceed the %dMB ceiling",
            jobs, safe_jobs, jobs, memory_mb, MAX_TOTAL_MEMORY_MB,
        )

    cells = [(bot_name, opp, k) for opp in opponents for k in budgets]
    results = run_cells(
        cells,
        registry=registry,
        engine_dir=engine,
        jobs=safe_jobs,
        timeout=timeout,
        memory_mb=memory_mb,
        progress=progress,
    )

    # run_cells returns completion order; group by opponent. `outcomeG (l, r)`
    # is only ever called with our bot on the left here, so `r.right` is the
    # opponent and no swap normalization is needed.
    grouped: dict[str, list[CellResult]] = {opp: [] for opp in opponents}
    for r in results:
        grouped.setdefault(r.right, []).append(r)

    return BotProfile(
        bot_name=bot_name,
        cells=tuple(_classify(opp, grouped.get(opp, [])) for opp in opponents),
        budgets=tuple(budgets),
        raw=tuple(results),
    )

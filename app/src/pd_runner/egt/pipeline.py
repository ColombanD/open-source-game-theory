"""The `(t, α)` sweep driver: tau tournaments -> the four EGT stages.

Two jobs, in order:

1. **Run directories.** The four stages pass a numeric payoff CSV between
   them, so each analysed matrix needs its own directory. `RunPaths` keys one
   by `(zoo, t, α)` plus a hash of the cells, and `run_stages` executes
   ii.a -> ii.d inside it.

2. **The sweep.** `sweep` walks a `(t, α)` grid, but the grid is NOT the unit
   of work: **distinct MATRICES are**. Two grid points that produce the same
   action-pair cells produce the same EGT answer, so they are analysed once
   and the result is shared. This matters because the Nash stage costs ~50s
   on an 11-type game while a tau tournament costs milliseconds — a 10x10
   grid is ~90 minutes if you analyse every point and typically a handful of
   minutes if you analyse every distinct matrix.

Why there are so few distinct matrices: `tau_play` thresholds a cooperation
mass at α, and only finitely many masses are achievable, so the phase diagram
is piecewise constant in α with breakpoints at those masses (see
`tau.play.alpha_breakpoints`). `alpha_phase_representatives` samples the
MIDPOINT of each phase rather than gridding blindly, which is both exact and
cheaper. The t dimension has no such structure — σ is continuous in t — so t
is gridded, and dedup catches the repeats.

Nothing here is Lean- or LLM-backed: it is matrix arithmetic over an outcome
table that the engine already certified.

**One asymmetry to know about.** A swept matrix never contains the "N"
(proven non-termination) state, even on a zoo that has one: `tau_play`
thresholds a cooperation mass, and `cooperates()` tests `== "C"`, so an "N"
base cell counts as not-cooperating and the tau lift emits a real D. A TauBot
always terminates, even when the bot it lifts does not. So on the enlarged
zoo the base matrix analyses 15 types (MirrorBot dropped by the
non-termination policy) while every swept matrix analyses 16. That is a
property of the tau lift, not of this module — but compare base-vs-swept
results with it in mind.
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable, Iterable, Sequence

from pd_runner.egt.ingest import (
    DEFAULT_B,
    DEFAULT_C,
    NonTerminationPolicy,
    PayoffMatrix,
    payoff_matrix_from_tournament,
)
from pd_runner.tau.matrix import DEFAULT_ZOO, TauMatrix, get_zoo
from pd_runner.tau.play import alpha_breakpoints
from pd_runner.tau.signal import (
    behavioral_distance_matrix,
    signal_family_at_temperature,
    temperature_for_transparency,
)
from pd_runner.tau.sweep import TournamentResult, run_tournament

# Default output root, ANCHORED to `app/` rather than the current directory.
#
# This was `Path("generated/egt")` until 2026-08-10, and a relative default
# silently changes meaning with cwd: run from `app/` it lands in
# `app/generated/egt/` (gitignored), run from the repo root it lands in
# `./generated/egt/` (not ignored), dumping ~120 artefact files into git
# status. Anchoring to the package matches `config.load_paths`, which derives
# every other generated directory the same way.
#
# `--out-root` still accepts a relative path and still resolves against cwd —
# that is an explicit choice by the caller, not a silent default.
# parents[3] is `app/` — this file is app/src/pd_runner/egt/pipeline.py, one
# level deeper than config.py, which uses parents[2] for the same directory.
DEFAULT_OUT_ROOT = Path(__file__).resolve().parents[3] / "generated" / "egt"

# Stage keys, in dependency order. ii.a writes the numeric CSV the rest read.
STAGES: tuple[str, ...] = (
    "ess", "invasion", "faces", "nash", "replicator", "moran",
)


def cells_fingerprint(payoff: PayoffMatrix) -> str:
    """A short stable hash of the action-pair cells + bot order.

    This is the identity of an ANALYSIS: two `(t, α)` points with the same
    fingerprint have the same payoff matrix and therefore the same EGT
    results, so they share one run directory.
    """
    from pd_runner.egt.nash.loader import hash_payoff_matrix

    return hash_payoff_matrix(payoff)[:12]


def _fmt_dial(x: float | None) -> str:
    """Format a dial in [0, 1] for a directory name.

    0.62 -> '062', 1.0 -> '100', 0.0 -> '000', None -> 'na'. Fixed-width
    hundredths keep the integer part: dropping it made t=1.0 and t=0.0 collide.
    """
    if x is None:
        return "na"
    return f"{round(x * 100):03d}"


@dataclass(frozen=True)
class RunPaths:
    """Where one analysed matrix's artefacts live."""

    root: Path
    zoo: str
    t: float | None
    alpha: float | None
    fingerprint: str
    # The σ family the sweep ran on (`tau.channels`). "behavioral" — the
    # historical default — keeps the original directory naming, so every
    # pre-2026-09-01 artefact path stays valid; other families carry their key
    # in the name so two families can never share (and silently clobber) a
    # run directory.
    family: str = "behavioral"

    @property
    def run_dir(self) -> Path:
        return self.root / "runs" / self.name

    @property
    def name(self) -> str:
        fam = "" if self.family == "behavioral" else f"{self.family}_"
        return f"{self.zoo}_{fam}t{_fmt_dial(self.t)}_a{_fmt_dial(self.alpha)}_{self.fingerprint}"

    def stage_dir(self, stage: str) -> Path:
        return self.run_dir / stage

    @property
    def numeric_csv(self) -> Path:
        """The inter-stage contract: written by ii.a, read by ii.b-ii.d."""
        return self.stage_dir("ess") / "payoff_matrix_numeric.csv"

    @property
    def ess_assumptions(self) -> Path:
        return self.stage_dir("ess") / "assumptions.json"

    @property
    def ess_summary(self) -> Path:
        return self.stage_dir("ess") / "ess_summary.csv"

    @classmethod
    def for_matrix(cls, payoff: PayoffMatrix, root: Path = DEFAULT_OUT_ROOT,
                   family: str = "behavioral") -> "RunPaths":
        return cls(
            root=Path(root),
            zoo=payoff.zoo or "unknown",
            t=payoff.t,
            alpha=payoff.alpha,
            fingerprint=cells_fingerprint(payoff),
            family=family,
        )


@dataclass
class StageOutcome:
    """What one stage did — including failing, which must not be silent."""

    stage: str
    ok: bool
    seconds: float
    error: str | None = None
    summary: dict = field(default_factory=dict)


@dataclass
class RunResult:
    """One analysed matrix: its paths, its stage outcomes, its headline numbers."""

    paths: RunPaths
    payoff: PayoffMatrix
    stages: list[StageOutcome]
    # Grid points that map to THIS matrix. len > 1 means dedup saved work.
    grid_points: list[tuple[float, float]] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return all(s.ok for s in self.stages)

    @property
    def failed_stages(self) -> list[str]:
        return [s.stage for s in self.stages if not s.ok]

    def write_summary(self) -> None:
        """(Re)write `summary.json`.

        Called again whenever a further grid point is found to map onto this
        matrix, so the recorded `grid_points` stays complete.
        """
        self.paths.run_dir.mkdir(parents=True, exist_ok=True)
        (self.paths.run_dir / "summary.json").write_text(
            json.dumps(self.summary(), indent=2)
        )

    def summary(self) -> dict:
        return {
            "run": self.paths.name,
            "zoo": self.paths.zoo,
            "family": self.paths.family,
            "t": self.paths.t,
            "alpha": self.paths.alpha,
            "fingerprint": self.paths.fingerprint,
            "n_types": len(self.payoff),
            "bots": list(self.payoff.bots),
            "excluded_bots": list(self.payoff.excluded_bots),
            "is_fully_proven": self.payoff.is_fully_proven,
            "grid_points": [list(p) for p in self.grid_points],
            "n_grid_points": len(self.grid_points),
            "ok": self.ok,
            "failed_stages": self.failed_stages,
            "stages": {
                s.stage: {
                    "ok": s.ok,
                    "seconds": round(s.seconds, 3),
                    "error": s.error,
                    **s.summary,
                }
                for s in self.stages
            },
        }


# --------------------------------------------------------------------------
# Stage execution
# --------------------------------------------------------------------------


def run_stages(
    payoff: PayoffMatrix,
    paths: RunPaths,
    stages: Sequence[str] = STAGES,
    atol: float = 1e-12,
    faces_tol: float = 1e-10,
    max_support_size: int | None = None,
    cycle_cap: int = 10_000,
    seed: int = 20260514,
    render: bool = True,
    lrsnash_bin: str = "lrsnash",
    replicator_samples: int = 200,
    moran_populations: tuple[int, ...] = (10, 50, 100),
    moran_betas: tuple[float, ...] = (0.01, 0.1, 1.0),
    on_event: Callable[[str], None] | None = None,
) -> list[StageOutcome]:
    """Run the requested stages over one payoff matrix, in dependency order.

    A stage that raises is RECORDED and the run continues to the next stage —
    except that everything downstream of a failed `ess` is skipped, since they
    read the CSV it writes. Failures are never silent: they land in the
    returned `StageOutcome` list and in `summary.json`.
    """
    from pd_runner.egt.faces.run import run_faces
    from pd_runner.egt.invasion.cli import run_invasion
    from pd_runner.egt.moran.run import run_moran
    from pd_runner.egt.nash.cli import run_pipeline as run_nash
    from pd_runner.egt.replicator.run import run_replicator
    from pd_runner.egt.static_analysis.cli import run_ess

    def emit(msg: str) -> None:
        if on_event is not None:
            on_event(msg)

    paths.run_dir.mkdir(parents=True, exist_ok=True)
    outcomes: list[StageOutcome] = []
    ess_ok = False

    for stage in stages:
        if stage != "ess" and stage in (
            "invasion", "faces", "nash", "replicator", "moran",
        ) and not ess_ok:
            # ii.b-ii.d read the numeric CSV that ii.a writes.
            if not paths.numeric_csv.exists():
                outcomes.append(StageOutcome(
                    stage=stage, ok=False, seconds=0.0,
                    error="skipped: stage 'ess' did not produce a numeric matrix",
                ))
                continue

        out_dir = paths.stage_dir(stage)
        t0 = time.perf_counter()
        emit(f"[{paths.name}] {stage}: start")
        try:
            summary: dict = {}
            if stage == "ess":
                result = run_ess(payoff, out_dir, atol=atol)
                summary = {
                    "n_pure_ess": sum(1 for s in result.summary if s.is_ESS),
                    "n_types": len(payoff),
                }
                ess_ok = True
            elif stage == "invasion":
                G_s, G_w, analysis, _agree, backend = run_invasion(
                    payoff, paths.numeric_csv, out_dir,
                    ess_summary=paths.ess_summary,
                    inherited_assumptions=paths.ess_assumptions,
                    atol=atol, cycle_cap=cycle_cap, seed=seed, render=render,
                )
                summary = {
                    "edges_strict": G_s.number_of_edges(),
                    "edges_weak": G_w.number_of_edges(),
                    "n_sccs": len(analysis.sccs),
                    "n_cycles": analysis.cycles.n_cycles_total,
                    "layout_backend": backend,
                }
            elif stage == "faces":
                df = run_faces(
                    paths.numeric_csv, out_dir,
                    inherited_assumptions=paths.ess_assumptions,
                    tol=faces_tol, max_support_size=max_support_size,
                    progress=False,
                )
                counts = df["overall_class"].value_counts().to_dict()
                summary = {
                    "n_supports": int(len(df)),
                    "by_class": {str(k): int(v) for k, v in counts.items()},
                    "enumeration_complete": max_support_size is None,
                }
            elif stage == "nash":
                nash_run = run_nash(
                    payoff=payoff,
                    numeric_csv=paths.numeric_csv,
                    out_dir=out_dir,
                    inherited_assumptions_path=paths.ess_assumptions,
                    lrsnash_bin=lrsnash_bin,
                )
                prov = json.loads((nash_run / "provenance.json").read_text())
                summary = {
                    "run_dir": str(nash_run.relative_to(out_dir)),
                    "n_extreme_NE": prov["n_extreme_NE"],
                    "n_components": prov["n_components"],
                    "cross_check_performed": prov["cross_check_performed"],
                }
            elif stage == "replicator":
                basins = run_replicator(
                    paths.numeric_csv, out_dir,
                    inherited_assumptions=paths.ess_assumptions,
                    n_samples=replicator_samples, seed=seed,
                )
                largest = max(
                    (basins.basin_fraction(a) for a in basins.attractors),
                    default=0.0,
                )
                summary = {
                    "n_attractors": len(basins.attractors),
                    "n_unconverged": basins.n_unconverged,
                    "all_converged": basins.all_converged,
                    "largest_basin": round(largest, 6),
                    "dominant_support": next(
                        (a.support(basins.names) for a in sorted(
                            basins.attractors, key=lambda a: -a.n_interior)),
                        [],
                    ),
                }
            elif stage == "moran":
                points = run_moran(
                    paths.numeric_csv, out_dir,
                    inherited_assumptions=paths.ess_assumptions,
                    populations=moran_populations, betas=moran_betas,
                )
                # The strongest-selection, largest-population point is the
                # headline; the rest live in the artefacts.
                headline = max(points, key=lambda r: (r.beta, r.population))
                summary = {
                    "n_points": len(points),
                    "all_converged": all(r.converged for r in points),
                    "headline": {
                        "population": headline.population,
                        "beta": headline.beta,
                        "stochastically_stable": headline.stochastically_stable(),
                    },
                }
            else:
                raise ValueError(f"unknown stage {stage!r}; choose from {STAGES}")

            secs = time.perf_counter() - t0
            outcomes.append(StageOutcome(stage, True, secs, summary=summary))
            emit(f"[{paths.name}] {stage}: ok ({secs:.1f}s)")
        except Exception as exc:  # noqa: BLE001 — recorded, not swallowed
            secs = time.perf_counter() - t0
            outcomes.append(StageOutcome(
                stage, False, secs, error=f"{type(exc).__name__}: {exc}",
            ))
            emit(f"[{paths.name}] {stage}: FAILED ({type(exc).__name__}: {exc})")

    return outcomes


def analyse_matrix(
    payoff: PayoffMatrix,
    out_root: Path = DEFAULT_OUT_ROOT,
    grid_points: Sequence[tuple[float, float]] = (),
    family: str = "behavioral",
    **kwargs,
) -> RunResult:
    """Run the stages over one payoff matrix and write its `summary.json`."""
    paths = RunPaths.for_matrix(payoff, out_root, family=family)
    stage_outcomes = run_stages(payoff, paths, **kwargs)
    result = RunResult(
        paths=paths,
        payoff=payoff,
        stages=stage_outcomes,
        grid_points=list(grid_points),
    )
    result.write_summary()
    return result


# --------------------------------------------------------------------------
# The (t, α) sweep
# --------------------------------------------------------------------------


def alpha_phase_representatives(
    matrix: TauMatrix,
    t: float,
    distances: dict[tuple[str, str], int] | None = None,
    quantize: int = 9,
    channel: dict | None = None,
) -> list[float]:
    """One α per PHASE at this transparency, sampled at the phase midpoint.

    `tau_play` compares a cooperation mass against α, and only finitely many
    masses are achievable, so behavior is constant between consecutive
    breakpoints. Taking the midpoint of each interval avoids sitting exactly
    on a breakpoint, where the `≥ α` tie-break makes the answer sensitive to
    float noise.

    Every distinct α-behavior at this t is represented — no grid density to
    tune. **But note the scale**: at `t = 1` the masses are a point mass and
    there are ~3 phases, while at `t < 1` the softmax spreads them so that
    almost every (bot, signal) pair has its own mass and there are ~|zoo|²
    phases. Most of those phases yield the SAME payoff matrix, so this is
    exact but far from minimal as a unit of work.

    Use it to characterize the α axis at ONE transparency (that is what
    `--alpha-phases` does). For a `(t, α)` sweep, pass explicit α values:
    the sweep dedups by matrix anyway, so extra α points buy little and each
    distinct matrix costs a full Nash enumeration.
    """
    if channel is None:
        dist = distances if distances is not None else behavioral_distance_matrix(matrix)
        temperature = temperature_for_transparency(matrix, t, distances=dist)
        channel = signal_family_at_temperature(matrix, temperature, dist)

    breaks = alpha_breakpoints(matrix, channel, quantize=quantize)
    # Breakpoints are the achievable masses; phases are the gaps between them,
    # plus the region above the largest mass (where everyone defects).
    edges = sorted({0.0, *breaks, 1.0})
    reps: list[float] = []
    for lo, hi in zip(edges, edges[1:]):
        if hi - lo > 10**-quantize:
            reps.append(round((lo + hi) / 2, quantize))
    # Always include the extremes: α=0 (unconditional C) and α=1 (unanimity).
    return sorted({0.0, *reps, 1.0})


def linear_ts(steps: int) -> list[float]:
    """`steps` transparency dials from 1.0 down to 0.0 inclusive."""
    steps = max(int(steps), 2)
    return [round(1.0 - i / (steps - 1), 6) for i in range(steps)]


# The default α values: the caution thresholds the tau report already sweeps,
# plus the two extremes. NOT `alpha_phase_representatives` — see its docstring;
# at t < 1 that yields ~|zoo|² phases per t, and each distinct matrix costs a
# full exact-rational Nash enumeration (~50s at N=11).
DEFAULT_ALPHAS: tuple[float, ...] = (0.0, 0.3, 0.45, 0.62, 0.8, 1.0)


@dataclass
class SweepResult:
    """A whole `(t, α)` sweep: the distinct matrices and what they cost."""

    zoo: str
    runs: list[RunResult]
    n_grid_points: int
    seconds: float
    out_root: Path
    family: str = "behavioral"

    @property
    def summary_path(self) -> Path:
        """`sweep_summary.json` for the behavioral family (the historical name
        the report reads); `sweep_summary_<family>.json` otherwise, so two
        families swept into one root never clobber each other."""
        name = ("sweep_summary.json" if self.family == "behavioral"
                else f"sweep_summary_{self.family}.json")
        return Path(self.out_root) / name

    @property
    def n_distinct(self) -> int:
        return len(self.runs)

    @property
    def ok(self) -> bool:
        """True when every stage of every analysed matrix succeeded."""
        return all(r.ok for r in self.runs)

    def summary(self) -> dict:
        return {
            "zoo": self.zoo,
            "family": self.family,
            "n_grid_points": self.n_grid_points,
            "n_distinct_matrices": self.n_distinct,
            "dedup_saved": self.n_grid_points - self.n_distinct,
            "seconds": round(self.seconds, 2),
            "ok": all(r.ok for r in self.runs),
            "runs": [r.summary() for r in self.runs],
        }


def sweep(
    zoo: str = DEFAULT_ZOO,
    ts: Sequence[float] | None = None,
    alphas: Sequence[float] | str | None = None,
    out_root: Path = DEFAULT_OUT_ROOT,
    stages: Sequence[str] = STAGES,
    family: str = "behavioral",
    b: float = DEFAULT_B,
    c: float = DEFAULT_C,
    non_termination: NonTerminationPolicy = "exclude",
    non_termination_payoff: float | None = None,
    t_steps: int = 6,
    on_event: Callable[[str], None] | None = None,
    **stage_kwargs,
) -> SweepResult:
    """Analyse every DISTINCT payoff matrix arising on the `(t, α)` grid.

    Grid points that yield identical action-pair cells share a single
    analysis; `RunResult.grid_points` records which points mapped to each
    matrix. On a uniform grid this typically halves the work, because the
    `(t, α)` phase diagram is piecewise constant.

    `alphas=None` uses `DEFAULT_ALPHAS`. Pass `alphas="phases"` to enumerate
    one α per phase at each t — exact, but ~|zoo|² points per t
    (see `alpha_phase_representatives`), so reserve it for a single t or for
    stages far cheaper than Nash.

    `family` selects the σ channel (`tau.channels.all_families`): "behavioral"
    (the historical default — softmax over own-action rows), "syntactic" (AST
    distance) or "epsilon" (identity-based null control; the family the
    `body+natives` aggregator ablation runs on). All families expose the same
    normalized-MI transparency dial, so `t` means the same thing across them
    and cross-family results at matched t are comparable. Non-behavioral runs
    carry the family in their run-directory names and write
    `sweep_summary_<family>.json`, so families never clobber each other in one
    out_root. (The HTML report still reads the behavioral summary only.)
    """
    t0 = time.perf_counter()

    def emit(msg: str) -> None:
        if on_event is not None:
            on_event(msg)

    named = get_zoo(zoo)
    matrix = named.load()
    distances = behavioral_distance_matrix(matrix)
    if family == "behavioral":
        fam = None   # the legacy path — byte-identical artefacts and naming
    else:
        from pd_runner.tau.channels import all_families

        families = all_families(matrix)
        if family not in families:
            raise ValueError(
                f"unknown σ family {family!r}; choose one of {sorted(families)}")
        fam = families[family]
    t_values = list(ts) if ts is not None else linear_ts(t_steps)

    by_fingerprint: dict[str, RunResult] = {}
    order: list[str] = []
    n_points = 0

    for t in t_values:
        if alphas is None:
            a_values = list(DEFAULT_ALPHAS)
        elif isinstance(alphas, str):
            if alphas != "phases":
                raise ValueError(
                    f"alphas must be a sequence or the literal 'phases', got {alphas!r}"
                )
            a_values = alpha_phase_representatives(
                matrix, t, distances,
                channel=fam.channel(t) if fam is not None else None)
        else:
            a_values = list(alphas)
        for alpha in a_values:
            n_points += 1
            result: TournamentResult = run_tournament(
                matrix, t, alpha, distances, family=fam)
            payoff = payoff_matrix_from_tournament(
                result,
                bots=matrix.bots,
                b=b, c=c,
                non_termination=non_termination,
                non_termination_payoff=non_termination_payoff,
                stipulated_cells=matrix.hypothetical_cells,
                zoo=zoo,
            )
            fp = cells_fingerprint(payoff)
            if fp in by_fingerprint:
                # Same cells => same EGT answer. Record the point and reuse.
                existing = by_fingerprint[fp]
                existing.grid_points.append((t, alpha))
                existing.write_summary()
                emit(f"(t={t}, α={alpha}) -> matrix {fp} (already analysed)")
                continue

            emit(f"(t={t}, α={alpha}) -> matrix {fp} — analysing")
            run = analyse_matrix(
                payoff, out_root, grid_points=[(t, alpha)],
                family=family, stages=stages, on_event=on_event, **stage_kwargs,
            )
            by_fingerprint[fp] = run
            order.append(fp)

    sweep_result = SweepResult(
        zoo=zoo,
        runs=[by_fingerprint[fp] for fp in order],
        n_grid_points=n_points,
        seconds=time.perf_counter() - t0,
        out_root=Path(out_root),
        family=family,
    )

    out_root = Path(out_root)
    out_root.mkdir(parents=True, exist_ok=True)
    sweep_result.summary_path.write_text(
        json.dumps(sweep_result.summary(), indent=2)
    )
    emit(
        f"sweep done: {sweep_result.n_distinct} distinct matrices from "
        f"{n_points} grid points in {sweep_result.seconds:.1f}s"
    )
    return sweep_result


def main() -> None:
    import argparse

    from pd_runner.tau.matrix import ZOOS

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--zoo", default=DEFAULT_ZOO, choices=sorted(ZOOS))
    p.add_argument("--t-steps", type=int, default=6,
                   help="linear transparency dials from 1.0 down to 0.0")
    p.add_argument("--ts", type=str, default=None,
                   help="explicit comma-separated t values (overrides --t-steps)")
    p.add_argument("--alphas", type=str, default=None,
                   help=(
                       "comma-separated α values (default: "
                       f"{','.join(str(a) for a in DEFAULT_ALPHAS)}), or the "
                       "literal 'phases' for one α per behavioral phase — exact "
                       "but ~|zoo|^2 points per t, so pair it with a single t "
                       "or with --stages ess,invasion,faces"
                   ))
    p.add_argument("--family", type=str, default="behavioral",
                   choices=("behavioral", "epsilon", "syntactic"),
                   help=("the sigma channel family (tau.channels); all three share "
                         "the normalized-MI t dial, so results at matched t are "
                         "cross-family comparable"))
    p.add_argument("--stages", type=str, default=",".join(STAGES),
                   help=f"comma-separated subset of {STAGES}")
    p.add_argument("--out-root", type=Path, default=DEFAULT_OUT_ROOT)
    p.add_argument("--max-support-size", type=int, default=None)
    p.add_argument("--no-render", action="store_true",
                   help="skip invasion-graph figures (faster in a sweep)")
    args = p.parse_args()

    if args.alphas is None:
        alphas = None
    elif args.alphas.strip() == "phases":
        alphas = "phases"
    else:
        alphas = [float(x) for x in args.alphas.split(",")]

    result = sweep(
        zoo=args.zoo,
        ts=[float(x) for x in args.ts.split(",")] if args.ts else None,
        alphas=alphas,
        out_root=args.out_root,
        family=args.family,
        stages=tuple(s.strip() for s in args.stages.split(",") if s.strip()),
        t_steps=args.t_steps,
        max_support_size=args.max_support_size,
        render=not args.no_render,
        on_event=print,
    )

    print()
    print(f"zoo: {result.zoo}   family: {result.family}")
    print(f"grid points     : {result.n_grid_points}")
    print(f"distinct matrices: {result.n_distinct} "
          f"(dedup saved {result.n_grid_points - result.n_distinct} analyses)")
    print(f"wallclock       : {result.seconds:.1f}s")
    print(f"artefacts       : {result.out_root}/runs/")
    failed = [r for r in result.runs if not r.ok]
    if failed:
        print(f"FAILURES in {len(failed)} run(s):")
        for r in failed:
            print(f"  {r.paths.name}: {', '.join(r.failed_stages)}")


if __name__ == "__main__":
    main()

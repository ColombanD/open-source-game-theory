"""Where trajectories end up, and from how much of the state space.

Integrate from many starting mixes, group the endpoints, and the share of
starts reaching each group is its BASIN. This is the number the first four
stages cannot produce: they say which resting points EXIST, this says which
one a population actually reaches.

**Grouping is by SUPPORT, not by point.** On this zoo the endpoints do not
land on isolated equilibria: they spread across a connected face of
neutrally-stable rest points, so the population settles onto a *set* of
coexisting types but *where* on that set depends on where it started. Measured
on the default 11-bot matrix, 26 interior samples produced 26 distinct
endpoints (pairwise coordinate distances up to 0.45) sharing just 2 supports.

Clustering those by proximity would report 26 attractors each with a 3.8%
basin, which is arithmetically true and completely misleading — it invents 26
answers where the dynamics have 2. Grouping by which types survive gives the
invariant that is actually stable across starts, and the spread WITHIN a group
is reported (`spread`) rather than hidden, since a wide spread is exactly the
signal that the rest points form a continuum.

Three honesty rules run through the module:

  * A trajectory that did not converge is never assigned to an attractor. It
    is counted separately as `n_unconverged`, because a cycling or crawling
    path has not found a resting point and pretending otherwise would invent
    one. Convergence is a Nash test at two times (`dynamics.integrate`), not a
    small speed.
  * Basin fractions are shares of ALL interior samples, converged or not, so
    the fractions and the unconverged share add up to 1 (until 2026-11-10 the
    denominator was the converged starts, which inflated every basin of a
    game with cycles). Vertices are tracked separately — they are a
    measure-zero set, so folding them in would quietly inflate whichever
    monoculture they sit on.
  * A start that converges within tolerance to a rest point the exact dynamics
    LEAVES is flagged `metastable`, with the types that invade it. Full
    defection {DefectBot, OBot} is the paper's case: DupocBot ties there and
    earns more against itself, so it invades at second order — arbitrarily
    slowly when it starts rare. Such a basin is a statement about the horizon
    (`max_horizon`), not an attractor of the dynamics.

**Nash components.** When the extreme equilibria of the game are supplied
(`equilibria`, from the Nash stage), every converged endpoint is also matched
to the Nash COMPONENT it lies in, and `components` aggregates the basins by
component. A continuum of rest points — several supports here — is then ONE
entry, which is the invariant to quote. The matching: label a strategy by the
types it does not play and the types that are best replies to it; the extreme
strategies carrying at least the endpoint's labels span a face of the
best-response polytope, all its pairings are equilibria, so they lie in one
component, and the endpoint must sit within `_MAX_DISTANCE` of their hull.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Sequence

import numpy as np  # type: ignore
from scipy.optimize import nnls  # type: ignore

from .dynamics import (
    HORIZON,
    MAX_HORIZON,
    MAX_RHS_EVALS,
    TOL,
    Trajectory,
    integrate,
    nash_labels,
    simplex_samples,
)

# A game in which at least half of the first CYCLE_PROBE interior starts run
# out of evaluations is a cycling game: each such start costs the full budget
# (about a second), so 1000 starts would cost a quarter of an hour for a
# fraction the first hundred already estimate. The remaining starts are then
# not integrated. The result says so (`truncated_cycling`), and its basins and
# intervals are over the starts actually integrated — the first CYCLE_PROBE
# independent draws, so the estimates stay unbiased, only wider.
CYCLE_PROBE = 100

# How far a converged endpoint may lie from the hull of its component's face.
_MAX_DISTANCE = 1e-4
_Z95 = 1.959963984540054  # the standard normal's 97.5% quantile

# One extreme equilibrium of the game: (row strategy, column strategy, component id).
ExtremeEquilibrium = tuple[Sequence[Fraction], Sequence[Fraction], int]


def wilson_interval(k: int, n: int) -> tuple[float, float]:
    """95% interval for a probability, from `k` successes in `n` independent trials."""
    if n == 0:
        return 0.0, 1.0
    p, z2 = k / n, _Z95 ** 2
    centre = (p + z2 / (2 * n)) / (1 + z2 / n)
    half = _Z95 * float(np.sqrt(p * (1 - p) / n + z2 / (4 * n * n))) / (1 + z2 / n)
    return max(0.0, centre - half), min(1.0, centre + half)


@dataclass(frozen=True)
class _Vertex:
    """An extreme strategy of the game's equilibria, with its labels."""

    x: np.ndarray
    present: frozenset[int]   # the types it plays
    best: frozenset[int]      # the types that are best replies to it
    component: int


def _vertices(A: np.ndarray, equilibria: Sequence[ExtremeEquilibrium]) -> list[_Vertex]:
    """Every extreme strategy, once, labelled in exact arithmetic."""
    exact = [[Fraction(str(a)) for a in row] for row in np.asarray(A).tolist()]
    out: dict[tuple[Fraction, ...], _Vertex] = {}
    for xi, eta, component in equilibria:
        for strategy in (tuple(Fraction(p) for p in xi), tuple(Fraction(p) for p in eta)):
            if strategy in out:
                continue
            payoffs = [sum((a * p for a, p in zip(row, strategy)), Fraction(0)) for row in exact]
            top = max(payoffs)
            out[strategy] = _Vertex(
                x=np.array([float(p) for p in strategy]),
                present=frozenset(i for i, p in enumerate(strategy) if p > 0),
                best=frozenset(i for i, v in enumerate(payoffs) if v == top),
                component=int(component),
            )
    return list(out.values())


def _locate(x: np.ndarray, present: frozenset[int], best: frozenset[int],
            vertices: list[_Vertex]) -> int | None:
    """The Nash component the converged endpoint `x` lies in, or None if it cannot be placed."""
    face = [v for v in vertices if v.present <= present and best <= v.best]
    if len({v.component for v in face}) != 1:
        return None
    V = np.column_stack([v.x for v in face])
    weights, _ = nnls(V, x)
    if weights.sum() <= 0:
        return None
    if float(np.abs(V @ (weights / weights.sum()) - x).max()) > _MAX_DISTANCE:
        return None
    return face[0].component


@dataclass
class Attractor:
    """One SUPPORT: which types survive, and how many starts end up there.

    `x` is the mean endpoint over the members — a representative, not a fixed
    point. When `spread` is large the members lie on a continuum and the mean
    is a summary of that set rather than a place the population sits.
    """

    support_key: tuple[int, ...]       # surviving type indices, sorted
    x: np.ndarray                      # mean endpoint of the members
    n_interior: int = 0                # converged interior starts reaching it
    n_vertex: int = 0                  # monoculture starts reaching it
    vertex_sources: list[str] = field(default_factory=list)
    members: list[np.ndarray] = field(default_factory=list, repr=False)
    # Interior members that sit on a rest point the exact dynamics leaves, and
    # the types that invade it at second order (`dynamics.second_order_invaders`).
    n_metastable: int = 0
    invaders: set[int] = field(default_factory=set)
    # The Nash component(s) of the interior members; empty when the Nash stage's
    # equilibria were not supplied. More than one would mean a support straddles
    # two components, which the matching reports rather than hides.
    components: set[int] = field(default_factory=set)

    @property
    def spread(self) -> float:
        """Largest coordinate deviation from the mean across members.

        Near 0: the endpoints coincide — a genuine point attractor.
        Large: a connected face of rest points; the population settles onto
        this set of types but its exact mix depends on where it started.
        """
        if len(self.members) < 2:
            return 0.0
        return float(max(np.max(np.abs(m - self.x)) for m in self.members))

    def support(self, names: list[str]) -> list[str]:
        """The types actually present, largest mean share first."""
        order = np.argsort(-self.x)
        return [names[i] for i in order if i in set(self.support_key)]

    def shares(self, names: list[str]) -> list[tuple[str, float]]:
        order = np.argsort(-self.x)
        keys = set(self.support_key)
        return [(names[i], float(self.x[i])) for i in order if i in keys]

    @property
    def is_monoculture(self) -> bool:
        return len(self.support_key) == 1


@dataclass
class BasinResult:
    """The whole basin estimate for one payoff matrix."""

    names: list[str]
    attractors: list[Attractor]
    n_interior_samples: int            # interior starts attempted
    n_interior_converged: int          # …of which converged
    n_unconverged: int                 # never assigned to an attractor
    n_vertex_samples: int
    seed: int
    horizon: float = HORIZON
    max_horizon: float = MAX_HORIZON
    tol: float = TOL
    n_budget_exhausted: int = 0        # unconverged starts that ran out of evaluations (cycles)
    n_metastable: int = 0              # converged interior starts on a rest point the dynamics leaves
    n_unlocated: int = 0               # converged interior starts no Nash component could be matched to
    n_interior_requested: int = 0      # interior starts asked for (n_interior_samples = integrated)
    truncated_cycling: bool = False    # stopped after CYCLE_PROBE starts, half or more out of evaluations
    has_components: bool = False       # were the game's extreme equilibria supplied?
    # component id -> [interior starts reaching it, of which metastable]
    component_counts: dict[int, list[int]] = field(default_factory=dict)
    component_supports: dict[int, set[tuple[int, ...]]] = field(default_factory=dict)
    horizons: dict[float, int] = field(default_factory=dict)   # horizon reached -> interior starts

    def basin_fraction(self, attractor: Attractor) -> float:
        """Share of ALL interior starts that converge to this attractor."""
        if self.n_interior_samples == 0:
            return 0.0
        return attractor.n_interior / self.n_interior_samples

    @property
    def unconverged_fraction(self) -> float:
        """Share of interior starts that did not converge by `max_horizon`."""
        if self.n_interior_samples == 0:
            return 0.0
        return (self.n_interior_samples - self.n_interior_converged) / self.n_interior_samples

    @property
    def all_converged(self) -> bool:
        return self.n_unconverged == 0

    def component_basins(self) -> list[dict]:
        """One entry per Nash component reached, largest basin first."""
        n = self.n_interior_samples
        out = []
        for cid, (count, metastable) in sorted(self.component_counts.items(),
                                               key=lambda kv: -kv[1][0]):
            lo, hi = wilson_interval(count, n)
            supports = sorted(self.component_supports.get(cid, ()), key=len)
            out.append({
                "component_id": cid,
                "n_interior": count,
                "basin_fraction": round(count / n, 6) if n else 0.0,
                "basin_ci95": [round(lo, 6), round(hi, 6)],
                "n_metastable": metastable,
                "bots": [self.names[i] for i in sorted({i for s in supports for i in s})],
                "n_supports": len(supports),
            })
        return out

    def summary(self) -> dict:
        n = self.n_interior_samples
        return {
            "n_attractors": len(self.attractors),
            "n_interior_samples": n,
            "n_interior_converged": self.n_interior_converged,
            "n_unconverged": self.n_unconverged,
            "n_budget_exhausted": self.n_budget_exhausted,
            "n_metastable": self.n_metastable,
            "n_unlocated": self.n_unlocated,
            "n_interior_requested": self.n_interior_requested or n,
            "truncated_cycling": self.truncated_cycling,
            "unconverged_fraction": round(self.unconverged_fraction, 6),
            "n_vertex_samples": self.n_vertex_samples,
            "all_converged": self.all_converged,
            "seed": self.seed,
            "horizon": self.horizon,
            "max_horizon": self.max_horizon,
            "tol": self.tol,
            "horizons_reached": {f"{h:g}": c for h, c in sorted(self.horizons.items())},
            "basin_denominator": "all interior samples",
            "has_components": self.has_components,
            "components": self.component_basins(),
            "attractors": [
                {
                    "support": a.support(self.names),
                    "shares": [[n_, round(s, 6)] for n_, s in a.shares(self.names)],
                    "is_monoculture": a.is_monoculture,
                    "spread": round(a.spread, 6),
                    "basin_fraction": round(self.basin_fraction(a), 6),
                    "basin_ci95": [round(v, 6) for v in wilson_interval(a.n_interior, n)],
                    "n_interior": a.n_interior,
                    "n_vertex": a.n_vertex,
                    "vertex_sources": a.vertex_sources,
                    "n_metastable": a.n_metastable,
                    "metastable": a.n_interior > 0 and a.n_metastable == a.n_interior,
                    "invaders": [self.names[i] for i in sorted(a.invaders)],
                    "components": sorted(a.components),
                }
                for a in sorted(self.attractors,
                                key=lambda a: -a.n_interior)
            ],
        }


def _support_key(x: np.ndarray, tol: float = TOL) -> tuple[int, ...]:
    """Indices of the types present: a share of at least `tol`, the convergence test's own cut."""
    return tuple(int(i) for i in np.flatnonzero(x >= tol))


def estimate_basins(
    A: np.ndarray,
    names: list[str],
    n_samples: int = 200,
    seed: int = 20260514,
    horizon: float = HORIZON,
    max_horizon: float = MAX_HORIZON,
    tol: float = TOL,
    max_rhs_evals: int = MAX_RHS_EVALS,
    equilibria: Sequence[ExtremeEquilibrium] | None = None,
    cycle_probe: int | None = CYCLE_PROBE,
) -> BasinResult:
    """Sample the simplex, integrate each start, group the endpoints.

    `cycle_probe`: stop after that many interior starts when at least half of
    them ran out of evaluations (a cycling game; see `CYCLE_PROBE`). `None`
    always integrates every start.

    Vertices (monocultures) are always included and tracked separately from
    the interior samples that produce the basin fractions. `equilibria` — the
    game's extreme equilibria with their component ids, from the Nash stage —
    turns on the matching of endpoints to Nash components.
    """
    n = len(names)
    A = np.asarray(A, dtype=float)
    if A.shape != (n, n):
        raise ValueError(f"A is {A.shape}, expected ({n}, {n})")

    vertices = simplex_samples(n, 0, seed, include_vertices=True,
                               include_uniform=False)
    interior = simplex_samples(n, n_samples, seed, include_vertices=False,
                               include_uniform=True)
    nash_vertices = _vertices(A, equilibria) if equilibria else []

    attractors: list[Attractor] = []
    by_support: dict[tuple[int, ...], Attractor] = {}
    result = BasinResult(
        names=list(names), attractors=attractors,
        n_interior_samples=len(interior), n_interior_converged=0, n_unconverged=0,
        n_vertex_samples=len(vertices), seed=seed, horizon=horizon,
        max_horizon=max_horizon, tol=tol, has_components=bool(nash_vertices),
        n_interior_requested=len(interior),
    )

    def run(x0: np.ndarray) -> Trajectory:
        return integrate(A, x0, horizon=horizon, max_horizon=max_horizon, tol=tol,
                         max_rhs_evals=max_rhs_evals)

    def place(traj: Trajectory) -> Attractor | None:
        """Attach a CONVERGED trajectory to its support group."""
        if not traj.converged:
            return None
        key = _support_key(traj.x, tol)
        found = by_support.get(key)
        if found is None:
            found = Attractor(support_key=key, x=traj.x.copy())
            by_support[key] = found
            attractors.append(found)
        found.members.append(traj.x.copy())
        # The representative is the running mean of the members.
        found.x = np.mean(np.array(found.members), axis=0)
        return found

    for k in range(len(vertices)):
        traj = run(vertices[k])
        target = place(traj)
        if target is None:
            result.n_unconverged += 1
            continue
        target.n_vertex += 1
        target.vertex_sources.append(names[k])

    for k in range(len(interior)):
        traj = run(interior[k])
        result.horizons[traj.horizon] = result.horizons.get(traj.horizon, 0) + 1
        target = place(traj)
        if target is None:
            result.n_unconverged += 1
            result.n_budget_exhausted += int(traj.budget_exhausted)
        if (cycle_probe is not None and k + 1 == cycle_probe < len(interior)
                and 2 * result.n_budget_exhausted >= cycle_probe):
            result.n_interior_samples = cycle_probe
            result.truncated_cycling = True
            stop_after_this = True
        else:
            stop_after_this = False
        if target is None:
            if stop_after_this:
                break
            continue
        target.n_interior += 1
        result.n_interior_converged += 1
        if traj.metastable:
            target.n_metastable += 1
            target.invaders.update(traj.second_order_invaders)
            result.n_metastable += 1
        if nash_vertices:
            labels = nash_labels(A, traj.x, tol)
            cid = _locate(traj.x, *labels, nash_vertices) if labels else None
            if cid is None:
                result.n_unlocated += 1
            else:
                target.components.add(cid)
                counts = result.component_counts.setdefault(cid, [0, 0])
                counts[0] += 1
                counts[1] += int(traj.metastable)
                result.component_supports.setdefault(cid, set()).add(target.support_key)
        if stop_after_this:
            break

    return result

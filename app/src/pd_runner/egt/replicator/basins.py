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

Two honesty rules run through the module:

  * A trajectory that did not converge is never assigned to an attractor. It
    is counted separately as `n_unconverged`, because a cycling or crawling
    path has not found a resting point and pretending otherwise would invent
    one.
  * Basin fractions are over CONVERGED interior samples only, and the
    denominator is reported alongside them. Vertices are tracked separately —
    they are a measure-zero set, so folding them in would quietly inflate
    whichever monoculture they sit on.
"""

from __future__ import annotations

from dataclasses import dataclass, field

import numpy as np  # type: ignore

from .dynamics import Trajectory, integrate, simplex_samples

# A type is "present" in an attractor above this share. Below it the type is
# a numerical residue of a dying component, not a member of the mixture.
_SUPPORT_TOL = 1e-3


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
    dt: float
    max_steps: int

    def basin_fraction(self, attractor: Attractor) -> float:
        """Share of CONVERGED interior starts reaching this attractor."""
        if self.n_interior_converged == 0:
            return 0.0
        return attractor.n_interior / self.n_interior_converged

    @property
    def all_converged(self) -> bool:
        return self.n_unconverged == 0

    def summary(self) -> dict:
        return {
            "n_attractors": len(self.attractors),
            "n_interior_samples": self.n_interior_samples,
            "n_interior_converged": self.n_interior_converged,
            "n_unconverged": self.n_unconverged,
            "n_vertex_samples": self.n_vertex_samples,
            "all_converged": self.all_converged,
            "seed": self.seed,
            "dt": self.dt,
            "max_steps": self.max_steps,
            "attractors": [
                {
                    "support": a.support(self.names),
                    "shares": [[n, round(s, 6)] for n, s in a.shares(self.names)],
                    "is_monoculture": a.is_monoculture,
                    "spread": round(a.spread, 6),
                    "basin_fraction": round(self.basin_fraction(a), 6),
                    "n_interior": a.n_interior,
                    "n_vertex": a.n_vertex,
                    "vertex_sources": a.vertex_sources,
                }
                for a in sorted(self.attractors,
                                key=lambda a: -a.n_interior)
            ],
        }


def _support_key(x: np.ndarray) -> tuple[int, ...]:
    """Indices of the types present above the residue threshold."""
    return tuple(int(i) for i in np.flatnonzero(x > _SUPPORT_TOL))


def estimate_basins(
    A: np.ndarray,
    names: list[str],
    n_samples: int = 200,
    seed: int = 20260514,
    dt: float = 0.1,
    max_steps: int = 50_000,
    tol: float = 1e-7,
) -> BasinResult:
    """Sample the simplex, integrate each start, cluster the endpoints.

    Vertices (monocultures) are always included and tracked separately from
    the interior samples that produce the basin fractions.
    """
    n = len(names)
    if A.shape != (n, n):
        raise ValueError(f"A is {A.shape}, expected ({n}, {n})")

    vertices = simplex_samples(n, 0, seed, include_vertices=True,
                               include_uniform=False)
    interior = simplex_samples(n, n_samples, seed, include_vertices=False,
                               include_uniform=True)

    attractors: list[Attractor] = []
    n_converged = 0
    n_unconverged = 0

    by_support: dict[tuple[int, ...], Attractor] = {}

    def place(traj: Trajectory) -> Attractor | None:
        """Attach a CONVERGED trajectory to its support group."""
        if not traj.converged:
            return None
        key = _support_key(traj.x)
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
        traj = integrate(A, vertices[k], dt=dt, max_steps=max_steps, tol=tol)
        target = place(traj)
        if target is None:
            n_unconverged += 1
            continue
        target.n_vertex += 1
        target.vertex_sources.append(names[k])

    for k in range(len(interior)):
        traj = integrate(A, interior[k], dt=dt, max_steps=max_steps, tol=tol)
        target = place(traj)
        if target is None:
            n_unconverged += 1
            continue
        target.n_interior += 1
        n_converged += 1

    return BasinResult(
        names=list(names),
        attractors=attractors,
        n_interior_samples=len(interior),
        n_interior_converged=n_converged,
        n_unconverged=n_unconverged,
        n_vertex_samples=len(vertices),
        seed=seed,
        dt=dt,
        max_steps=max_steps,
    )

"""The replicator equation, integrated on the simplex.

    ẋ_i = x_i · ( (A x)_i − xᵀ A x )

Type `i` grows when it earns more than the population average and shrinks when
it earns less. Two structural facts make this safe to integrate numerically:

  * the simplex is invariant — `Σ ẋ = 0`, so the proportions stay summing to 1;
  * every face is invariant — `x_i = 0` implies `ẋ_i = 0`, so a type that is
    absent never spontaneously appears. Selection alone introduces nothing;
    that is what stage (iv)'s mutation is for.

Both are asserted by the tests rather than assumed, because a solver that
drifts off the simplex silently produces plausible-looking nonsense.

`A` is NOT symmetric here (see `egt.ingest`), so the payoff to `i` against the
mix is `(A x)_i` with `A[i, j]` the row player's payoff — never `(xᵀ A)_i`.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np  # type: ignore


@dataclass(frozen=True)
class Trajectory:
    """One integrated path from a starting mix."""

    x0: np.ndarray            # starting mix
    x: np.ndarray             # final mix
    converged: bool           # speed fell below `tol` before the step budget
    steps: int
    max_speed_at_end: float   # ‖ẋ‖∞ at the final state


def replicator_field(A: np.ndarray, x: np.ndarray) -> np.ndarray:
    """`ẋ` at `x`. Rows of `A` are the row player, so fitness is `(A x)`."""
    fitness = A @ x
    average = float(x @ fitness)
    return x * (fitness - average)


def _project_to_simplex(x: np.ndarray) -> np.ndarray:
    """Clip negatives and renormalise.

    Explicit Euler can take a component microscopically negative near a face;
    left alone that component would then grow with the wrong sign and the
    trajectory would leave the simplex. Clipping restores face invariance
    exactly, which is a property of the dynamics rather than of the solver.
    """
    x = np.clip(x, 0.0, None)
    total = x.sum()
    if total <= 0:
        # Degenerate: everything died. Fall back to the uniform mix rather
        # than divide by zero — and the caller sees `converged=False`.
        return np.full_like(x, 1.0 / len(x))
    return x / total


def integrate(
    A: np.ndarray,
    x0: np.ndarray,
    dt: float = 0.1,
    max_steps: int = 50_000,
    tol: float = 1e-7,
) -> Trajectory:
    """Integrate the replicator equation from `x0` until it stops moving.

    Fourth-order Runge-Kutta with a fixed step, projected back onto the
    simplex after each step. Convergence is `‖ẋ‖∞ < tol`; hitting `max_steps`
    first is reported as `converged=False` rather than silently accepted — a
    cycling or slowly-crawling trajectory has NOT found an attractor, and
    treating its last point as one would invent a resting place.
    """
    x = _project_to_simplex(np.asarray(x0, dtype=float).copy())
    speed = float("inf")

    for step in range(1, max_steps + 1):
        k1 = replicator_field(A, x)
        speed = float(np.max(np.abs(k1)))
        if speed < tol:
            return Trajectory(np.asarray(x0, dtype=float), x, True, step, speed)

        k2 = replicator_field(A, _project_to_simplex(x + 0.5 * dt * k1))
        k3 = replicator_field(A, _project_to_simplex(x + 0.5 * dt * k2))
        k4 = replicator_field(A, _project_to_simplex(x + dt * k3))
        x = _project_to_simplex(x + (dt / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4))

    return Trajectory(np.asarray(x0, dtype=float), x, False, max_steps, speed)


def simplex_samples(
    n_types: int,
    n_samples: int,
    seed: int,
    include_vertices: bool = True,
    include_uniform: bool = True,
) -> np.ndarray:
    """Starting mixes: uniform over the simplex, plus the corners.

    Interior points come from a symmetric Dirichlet(1), which is the uniform
    distribution ON the simplex — normalising uniform `[0, 1]` draws is NOT
    (it concentrates near the centre and would bias every basin estimate
    toward whatever the centre flows to).

    The vertices are added deliberately: a monoculture is the starting point
    the ESS question asks about, and uniform sampling almost never lands on
    one. They are a measure-zero set, so they are reported separately rather
    than folded into the basin fractions.
    """
    rng = np.random.default_rng(seed)
    blocks = []
    if include_vertices:
        blocks.append(np.eye(n_types))
    if include_uniform:
        blocks.append(np.full((1, n_types), 1.0 / n_types))
    if n_samples > 0:
        blocks.append(rng.dirichlet(np.ones(n_types), size=n_samples))
    return np.vstack(blocks) if blocks else np.empty((0, n_types))

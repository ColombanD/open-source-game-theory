"""The replicator equation, integrated on the simplex.

    ẋ_i = x_i · g_i(x),     g_i(x) = (A x)_i − xᵀ A x

Type `i` grows when it earns more than the population average and shrinks when
it earns less. Two structural facts hold for the exact dynamics:

  * the simplex is invariant — `Σ ẋ = 0`, so the proportions stay summing to 1;
  * every face is invariant — `x_i = 0` implies `ẋ_i = 0`, so a type that is
    absent never spontaneously appears. Selection alone introduces nothing;
    that is what stage (iv)'s mutation is for.

**Integration.** A start is integrated in LOG-SHARES `z_i = log x_i`, where
`ż_i = g_i(x)` and `x = softmax(z)`, with an adaptive solver (LSODA). Shares
then stay positive and sum to 1 exactly however small they get, and a type at
share 1e-200 keeps its identity instead of being clipped to zero — which is
what a slow invasion needs. A start on a face is integrated on that face (its
absent types stay absent).

**Convergence is a NASH test at two times, not a speed test.** A start has
converged at horizon `H` when, at both `H/2` and `H`, the state is a symmetric
Nash equilibrium up to `tol` — no type grows faster than `tol`, and every type
is absent (`x_i < tol`) or ties the best (`g_i ≥ −tol`) — with the same absent
and tied sets at both times, and the state moved less than `tol` in between.

Until 2026-11-10 the test was `‖ẋ‖∞ < 1e-7` on a fixed-step RK4 run of at most
5000 time units. A small speed is not rest: a trajectory passing a saddle, or
leaving a rest point through a second-order invasion, is slow without being
anywhere it will stay. On rock-paper-scissors with losses larger than wins
(a heteroclinic cycle, nothing converges) that test reported every start as
converged to a monoculture; on the paper's `body8+trolls` zoo it reported a
27% basin for full defection, most of which leaves for cooperation later.

**Horizons.** A start that has not converged at `horizon` is integrated on, to
100× the time, until it converges or `max_horizon` is reached. Near a
monoculture that a neutral type ties with, the losing type dies out like 1/t,
not exponentially, and needs the longer horizons. So does a start that HAS
converged to a rest point the exact dynamics leaves (`second_order_invaders`):
it is integrated on as well, so that what remains flagged at `max_horizon` are
the escapes slower than that.

**Budget.** A cycling trajectory never converges and would cost the solver a
fixed number of evaluations per period, forever. Each start has a budget of
right-hand-side evaluations; running out is reported (`budget_exhausted`),
never passed off as convergence.

`A` is NOT symmetric here (see `egt.ingest`), so the payoff to `i` against the
mix is `(A x)_i` with `A[i, j]` the row player's payoff — never `(xᵀ A)_i`.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np  # type: ignore
from scipy.integrate import solve_ivp  # type: ignore

HORIZON = 1e5          # first horizon; payoffs are of order 1, so this is long
MAX_HORIZON = 1e9      # last horizon tried for a start that has not settled
HORIZON_FACTOR = 100.0
TOL = 1e-6             # absent share, tied growth rate, movement over [H/2, H]
RARE = 1e-3            # a tied type below this share is a candidate second-order invader
RTOL, ATOL = 1e-10, 1e-12   # integration error, per log-share
MAX_RHS_EVALS = 200_000     # per start; a cycle exhausts it, a settling path does not


@dataclass(frozen=True)
class Trajectory:
    """One integrated path from a starting mix."""

    x0: np.ndarray            # starting mix
    x: np.ndarray             # final mix
    converged: bool           # a symmetric Nash equilibrium up to tol at H/2 and H
    steps: int                # right-hand-side evaluations used
    max_speed_at_end: float   # ‖ẋ‖∞ at the final state
    horizon: float = 0.0      # the time integrated to
    budget_exhausted: bool = False   # ran out of evaluations (a cycle, typically)
    # Absent types that TIE the best reply and do better against themselves
    # than the residents do against them: they invade at second order, so the
    # exact dynamics leaves this rest point (it is not neutrally stable).
    second_order_invaders: tuple[int, ...] = ()

    @property
    def metastable(self) -> bool:
        """Converged within tolerance to a rest point the exact dynamics leaves."""
        return self.converged and bool(self.second_order_invaders)


def growth_rates(A: np.ndarray, x: np.ndarray) -> np.ndarray:
    """`g_i(x) = (Ax)_i − xᵀAx`: each type's payoff against `x`, minus the average."""
    fitness = A @ x
    return fitness - float(x @ fitness)


def replicator_field(A: np.ndarray, x: np.ndarray) -> np.ndarray:
    """`ẋ` at `x`. Rows of `A` are the row player, so fitness is `(A x)`."""
    return x * growth_rates(A, x)


def softmax(z: np.ndarray) -> np.ndarray:
    w = np.exp(z - z.max())
    return w / w.sum()


def nash_labels(
    A: np.ndarray, x: np.ndarray, tol: float = TOL,
) -> tuple[frozenset[int], frozenset[int]] | None:
    """`(present types, best replies)` when `(x, x)` is a Nash equilibrium up to `tol`.

    Present: `x_i ≥ tol`. Best reply: `g_i ≥ −tol`. `None` when some type grows
    faster than `tol` or a present type is not a best reply.
    """
    g = growth_rates(A, x)
    present = frozenset(int(i) for i in np.flatnonzero(x >= tol))
    best = frozenset(int(i) for i in np.flatnonzero(g >= -tol))
    if g.max() > tol or not present <= best:
        return None
    return present, best


def second_order_invaders(A: np.ndarray, x: np.ndarray, tol: float = TOL,
                          rare: float = RARE) -> tuple[int, ...]:
    """Rare types that invade the rest point `x` at second order.

    For a type `i` that ties the best reply, its growth rate at share `ε` is
    `ε(1−ε)·(A_ii − (xᵀA)_i)` to leading order: it grows iff it earns more
    against itself than the residents earn against it. Its share then grows
    like `1/(1/ε₀ − c·t)` — slowly, but it does leave. A first-order test (and
    any speed test) cannot see this.

    "Rare" is a share below `rare`, not below `tol`: a tied type caught at
    1.4e-6 on its way up is just above the absent cut, and treating it as a
    settled member of the mixture would report a state the dynamics is leaving
    as an attractor (the isolated `Pr[(C,C)] = 11/18` equilibrium of `body8`
    on the hinge side, with DefectBot creeping in, was the case in point). A
    genuine small member of a neutral mixture is not flagged: its coefficient
    `A_ii − (xᵀA)_i` is zero.
    """
    g = growth_rates(A, x)
    residents_vs = x @ A
    return tuple(
        int(i) for i in range(len(x))
        if x[i] < rare and abs(g[i]) <= tol and A[i, i] - residents_vs[i] > tol
    )


class _BudgetExhausted(Exception):
    pass


def _project_to_simplex(x: np.ndarray) -> np.ndarray:
    """Clip negatives and renormalise a STARTING mix (never a state mid-run)."""
    x = np.clip(np.asarray(x, dtype=float), 0.0, None)
    total = x.sum()
    if total <= 0:
        return np.full_like(x, 1.0 / len(x))
    return x / total


def integrate(
    A: np.ndarray,
    x0: np.ndarray,
    horizon: float = HORIZON,
    max_horizon: float = MAX_HORIZON,
    tol: float = TOL,
    max_rhs_evals: int = MAX_RHS_EVALS,
) -> Trajectory:
    """Integrate the replicator equation from `x0` until it settles.

    See the module docstring for the convergence test, the horizons and the
    budget. A start with absent types is integrated on its own face: those
    types stay absent, and "Nash" is then meant within the face (a monoculture
    is a rest point, whatever would invade it).
    """
    start = np.asarray(x0, dtype=float)
    x_start = _project_to_simplex(start)
    alive = np.flatnonzero(x_start > 0)
    sub = np.asarray(A, dtype=float)[np.ix_(alive, alive)]

    def embed(xs: np.ndarray) -> np.ndarray:
        full = np.zeros_like(x_start)
        full[alive] = xs
        return full

    def finish(xs: np.ndarray, converged: bool, evals: int, t: float,
               exhausted: bool = False) -> Trajectory:
        invaders = second_order_invaders(sub, xs, tol) if converged else ()
        return Trajectory(
            x0=start, x=embed(xs), converged=converged, steps=evals,
            max_speed_at_end=float(np.max(np.abs(replicator_field(sub, xs)))),
            horizon=t, budget_exhausted=exhausted,
            second_order_invaders=tuple(int(alive[i]) for i in invaders),
        )

    if len(alive) == 1:
        return finish(np.ones(1), True, 0, 0.0)

    evals = 0
    last = [np.log(x_start[alive])]
    reached = 0.0   # the latest time the solver evaluated: where a budget-exhausted run stops

    def rhs(t_now: float, z: np.ndarray) -> np.ndarray:
        nonlocal evals, reached
        evals += 1
        if evals > max_rhs_evals:
            raise _BudgetExhausted
        last[0], reached = z, float(t_now)
        return growth_rates(sub, softmax(z))

    z, t, H = last[0], 0.0, float(horizon)
    while True:
        try:
            sol = solve_ivp(rhs, (t, H), z, method="LSODA", t_eval=(H / 2, H),
                            rtol=RTOL, atol=ATOL)
        except _BudgetExhausted:
            return finish(softmax(last[0]), False, max_rhs_evals, reached, exhausted=True)
        if not sol.success or sol.y.shape[1] != 2:
            return finish(softmax(last[0]), False, evals, t)
        x_half, x_end = softmax(sol.y[:, 0]), softmax(sol.y[:, 1])
        end_labels = nash_labels(sub, x_end, tol)
        converged = (
            end_labels is not None
            and end_labels == nash_labels(sub, x_half, tol)
            and float(np.max(np.abs(x_end - x_half))) < tol
        )
        settled = converged and not second_order_invaders(sub, x_end, tol)
        if settled or H >= max_horizon:
            return finish(x_end, converged, evals, H)
        z, t, H = sol.y[:, 1], H, min(H * HORIZON_FACTOR, float(max_horizon))


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

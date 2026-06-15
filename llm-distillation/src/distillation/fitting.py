"""Fit an input cooperation profile to the convex hull of reference rows.

Given the reference matrix ``R`` (row ``i`` = reference vector ``r_i``) and an
input vector ``x in [0, 1]^N``, we seek a weight vector ``w`` on the simplex
(``w_i >= 0``, ``sum w_i = 1``) so that the fitted profile ``R^T w`` -- a convex
combination of the reference rows -- is as close to ``x`` as possible.

``R^T w`` ranges exactly over ``conv{r_i}``, the realizable set. A nonzero
residual therefore means *no* convex combination of library bots can reproduce
``x``: the input sits off the library manifold.

Distances implemented:

* **L2** -- ``min ||R^T w - x||_2`` over the simplex. A convex quadratic program;
  the fitted point is unique. Solved with ``scipy.optimize.minimize`` (SLSQP).
* **L1** -- ``min ||R^T w - x||_1``. Linear program via per-coordinate auxiliary
  variables for the absolute values; solved with ``scipy.optimize.linprog``.
* **Linf** -- ``min ||R^T w - x||_inf``. Linear program with a single slack
  bounding every coordinate's absolute deviation. Included as a second LP because
  it answers a different question ("minimise the *worst* per-opponent miss").
* **Expected Hamming** -- treats ``x`` and the fitted profile ``p = R^T w`` as
  Bernoulli means and minimises ``sum_j [p_j(1 - x_j) + (1 - p_j) x_j]``. This is
  *linear* in ``w``, so its optimum sits at a simplex vertex: it reduces to
  "pick the single library bot closest to ``x`` in expected Hamming". Reported as
  a cheap nearest-bot baseline rather than a true hull fit.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np
from scipy.optimize import linprog, minimize

# Below this weight a bot is treated as inactive (numerically zero mass).
WEIGHT_TOL = 1e-6
# Rank tolerance for the affine-independence (identifiability) check.
RANK_TOL = 1e-9


@dataclass(frozen=True)
class FitResult:
    """Outcome of fitting ``x`` to ``conv{r_i}`` under one distance."""

    metric: str
    weights: np.ndarray  # w*, on the simplex (length N)
    fitted: np.ndarray  # R^T w*, the fitted profile (length N)
    x: np.ndarray  # the input profile (length N)
    residual: float  # achieved distance ||R^T w* - x|| in the metric's norm
    identified: bool  # True iff active rows are affinely independent
    active: tuple[int, ...]  # indices of bots with non-negligible weight


def _active_indices(weights: np.ndarray, tol: float = WEIGHT_TOL) -> tuple[int, ...]:
    return tuple(int(i) for i in np.where(weights > tol)[0])


def is_identified(R: np.ndarray, active: tuple[int, ...], tol: float = RANK_TOL) -> bool:
    """Are the active reference rows affinely independent?

    Affine independence of ``{r_i : i in active}`` is equivalent to the vectors
    ``r_i - r_{i0}`` (i0 the first active index) being linearly independent, i.e.
    their matrix having rank ``len(active) - 1``. When this fails, the fitted
    point ``R^T w`` is still unique but ``w`` itself is not: mass can be shuffled
    among the dependent rows without changing the fit. The simplest failure is
    two identical active rows, between which mass splits arbitrarily.
    """
    if len(active) <= 1:
        return True
    rows = R[list(active)]
    diffs = rows[1:] - rows[0]
    rank = int(np.linalg.matrix_rank(diffs, tol=tol))
    return rank == len(active) - 1


def fit_l2(R: np.ndarray, x: np.ndarray) -> FitResult:
    """Minimise ``||R^T w - x||_2`` over the simplex (convex QP, unique point)."""
    n = R.shape[0]
    A = R.T  # columns are r_i; A @ w is the convex combination

    def objective(w: np.ndarray) -> float:
        resid = A @ w - x
        return float(resid @ resid)

    def gradient(w: np.ndarray) -> np.ndarray:
        return 2.0 * A.T @ (A @ w - x)

    w0 = np.full(n, 1.0 / n)
    constraints = {"type": "eq", "fun": lambda w: np.sum(w) - 1.0,
                   "jac": lambda w: np.ones(n)}
    bounds = [(0.0, 1.0)] * n
    result = minimize(
        objective, w0, jac=gradient, bounds=bounds, constraints=constraints,
        method="SLSQP", options={"ftol": 1e-12, "maxiter": 500},
    )
    if not result.success:
        raise RuntimeError(f"L2 solver failed: {result.message}")

    weights = np.clip(result.x, 0.0, None)
    weights = weights / weights.sum()
    return _build_result("L2", R, x, weights, ord_=2)


def fit_l1(R: np.ndarray, x: np.ndarray) -> FitResult:
    """Minimise ``||R^T w - x||_1`` over the simplex (LP)."""
    n = R.shape[0]
    A = R.T
    # Variables z = [w (n), t (n)], minimise sum(t) with t_j >= |(A w - x)_j|.
    c = np.concatenate([np.zeros(n), np.ones(n)])
    # A w - t <= x  ;  -A w - t <= -x
    A_ub = np.block([[A, -np.eye(n)], [-A, -np.eye(n)]])
    b_ub = np.concatenate([x, -x])
    A_eq = np.concatenate([np.ones(n), np.zeros(n)]).reshape(1, -1)
    b_eq = np.array([1.0])
    bounds = [(0.0, 1.0)] * n + [(0.0, None)] * n
    result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds)
    if not result.success:
        raise RuntimeError(f"L1 solver failed: {result.message}")
    weights = _clean_weights(result.x[:n])
    return _build_result("L1", R, x, weights, ord_=1)


def fit_linf(R: np.ndarray, x: np.ndarray) -> FitResult:
    """Minimise ``||R^T w - x||_inf`` over the simplex (LP)."""
    n = R.shape[0]
    A = R.T
    # Variables z = [w (n), t (1)], minimise t with t >= |(A w - x)_j| for all j.
    c = np.concatenate([np.zeros(n), np.ones(1)])
    A_ub = np.block([[A, -np.ones((n, 1))], [-A, -np.ones((n, 1))]])
    b_ub = np.concatenate([x, -x])
    A_eq = np.concatenate([np.ones(n), np.zeros(1)]).reshape(1, -1)
    b_eq = np.array([1.0])
    bounds = [(0.0, 1.0)] * n + [(0.0, None)]
    result = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds)
    if not result.success:
        raise RuntimeError(f"Linf solver failed: {result.message}")
    weights = _clean_weights(result.x[:n])
    return _build_result("Linf", R, x, weights, ord_=np.inf)


def fit_expected_hamming(R: np.ndarray, x: np.ndarray) -> FitResult:
    """Minimise expected Hamming distance (LP; optimum at a simplex vertex).

    ``sum_j [p_j(1 - x_j) + (1 - p_j) x_j]`` with ``p = R^T w`` is linear in
    ``w``: ``const + sum_i w_i * sum_j r_i(j)(1 - 2 x_j)``. The minimiser is the
    single reference bot with the smallest coefficient (nearest bot under
    expected Hamming), unless coefficients tie.
    """
    n = R.shape[0]
    A = R.T
    c = A.T @ (1.0 - 2.0 * x)  # per-bot coefficient; constant sum(x) dropped
    A_eq = np.ones((1, n))
    b_eq = np.array([1.0])
    bounds = [(0.0, 1.0)] * n
    result = linprog(c, A_eq=A_eq, b_eq=b_eq, bounds=bounds)
    if not result.success:
        raise RuntimeError(f"Expected-Hamming solver failed: {result.message}")
    weights = _clean_weights(result.x)
    fitted = A @ weights
    residual = float(np.sum(fitted * (1.0 - x) + (1.0 - fitted) * x))
    active = _active_indices(weights)
    return FitResult(
        metric="ExpectedHamming", weights=weights, fitted=fitted, x=x,
        residual=residual, identified=is_identified(R, active), active=active,
    )


def _clean_weights(weights: np.ndarray) -> np.ndarray:
    weights = np.clip(weights, 0.0, None)
    total = weights.sum()
    return weights / total if total > 0 else weights


def _build_result(
    metric: str, R: np.ndarray, x: np.ndarray, weights: np.ndarray, ord_: float
) -> FitResult:
    fitted = R.T @ weights
    residual = float(np.linalg.norm(fitted - x, ord=ord_))
    active = _active_indices(weights)
    return FitResult(
        metric=metric, weights=weights, fitted=fitted, x=x, residual=residual,
        identified=is_identified(R, active), active=active,
    )


# Registry of available distances, in report order.
FITTERS = {
    "L2": fit_l2,
    "L1": fit_l1,
    "Linf": fit_linf,
    "ExpectedHamming": fit_expected_hamming,
}


def fit_all(R: np.ndarray, x: np.ndarray) -> list[FitResult]:
    """Run every registered distance and return their fit results."""
    return [fitter(R, x) for fitter in FITTERS.values()]


def profile_stats(x: np.ndarray) -> dict[str, float]:
    """Metric-independent summaries of the input profile ``x``.

    * ``level`` = mean(x): overall cooperativeness.
    * ``sharpness`` = mean(|x_i - 0.5|): how decisive (near 0/1) the profile is.
    """
    return {
        "level": float(np.mean(x)),
        "sharpness": float(np.mean(np.abs(x - 0.5))),
    }

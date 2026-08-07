"""Per-support numerics: face equilibrium, replicator Jacobian, tangent
projection, eigenvalues, external invasion fitness.

The face equilibrium x_S* solves
        A_SS x = c · 1,   1ᵀ x = 1,
which is assembled as the (|S|+1)×(|S|+1) block system

        [ A_SS  -1 ] [ x ]   [ 0 ]
        [  1ᵀ    0 ] [ c ] = [ 1 ]

and solved via `scipy.linalg.solve`. The replicator Jacobian at x* on
the |S|-face is then projected onto the tangent space
{v ∈ R^|S| : 1ᵀv = 0} (basis from `scipy.linalg.null_space`) before its
eigenvalues are taken.
"""

from __future__ import annotations

import warnings
from dataclasses import dataclass
from typing import Optional, Sequence

import numpy as np  # type: ignore
from scipy import linalg as splinalg  # type: ignore
from scipy.linalg import LinAlgWarning  # type: ignore


@dataclass(frozen=True)
class FaceSolution:
    """Outcome of the per-support solve.

    `x` and `c` are None when the system is singular. `x` has length
    |S|; the caller scatters it back to the full N-vector.
    """

    x: Optional[np.ndarray]
    c: Optional[float]
    c_crosscheck: Optional[float]
    is_singular: bool
    is_interior: bool


def solve_face(A_S: np.ndarray, tol: float) -> FaceSolution:
    """Solve the (|S|+1)-block system for the face equilibrium.

    Returns a FaceSolution with `is_singular=True` and `x=None, c=None`
    when scipy reports a singular system or when the recovered x is not
    finite. Interior status is True iff every component of x exceeds
    `tol`.
    """
    k = A_S.shape[0]
    if A_S.shape != (k, k):
        raise ValueError(f"A_S must be square; got {A_S.shape}")

    ones = np.ones((k, 1))
    M = np.zeros((k + 1, k + 1), dtype=float)
    M[:k, :k] = A_S
    M[:k, k] = -1.0
    M[k, :k] = 1.0
    b = np.zeros(k + 1, dtype=float)
    b[k] = 1.0

    # Treat both hard failure (LinAlgError) and ill-conditioning
    # (LinAlgWarning, e.g. rcond << machine eps) as singular. With
    # integer payoffs and repeated row patterns, several sub-systems are
    # effectively singular even when scipy returns a finite-looking
    # result.
    try:
        with warnings.catch_warnings():
            warnings.simplefilter("error", LinAlgWarning)
            sol = splinalg.solve(M, b)
    except (splinalg.LinAlgError, LinAlgWarning):
        return FaceSolution(None, None, None, is_singular=True, is_interior=False)

    if not np.all(np.isfinite(sol)):
        return FaceSolution(None, None, None, is_singular=True, is_interior=False)

    x = sol[:k]
    c = float(sol[k])
    c_cross = float(x @ A_S @ x)
    is_interior = bool(np.all(x > tol))
    return FaceSolution(
        x=x,
        c=c,
        c_crosscheck=c_cross,
        is_singular=False,
        is_interior=is_interior,
    )


def replicator_jacobian(A_S: np.ndarray, x: np.ndarray) -> np.ndarray:
    """Replicator Jacobian J restricted to S, evaluated at x.

    Using the asymmetric-A formula
        J[a,b] = x_a · ( A[a,b] − (A x)_b − (Aᵀ x)_b ).
    Outside-S coordinates of the full x vector are zero, so (A x)_b for
    b ∈ S equals (A_S x_S)_b — we operate entirely on the slice.
    """
    Ax = A_S @ x
    ATx = A_S.T @ x
    return x[:, None] * (A_S - Ax[None, :] - ATx[None, :])


def tangent_eigvals(J: np.ndarray) -> np.ndarray:
    """Eigenvalues of J projected onto the tangent space {1ᵀv = 0}.

    Uses an orthonormal basis Q from `scipy.linalg.null_space` and
    returns `eig(Q.T @ J @ Q)`. For |S|=2 this returns a single
    eigenvalue. Returned as a complex ndarray.
    """
    k = J.shape[0]
    Q = splinalg.null_space(np.ones((1, k)))
    if Q.shape[1] != k - 1:
        # extremely unlikely numerically — null_space tolerance should
        # always pick out the k-1 directions orthogonal to 1
        raise RuntimeError(
            f"null_space returned a basis of unexpected dimension: {Q.shape}"
        )
    J_tan = Q.T @ J @ Q
    return splinalg.eig(J_tan, right=False)


def external_invasion_fitness(
    A: np.ndarray,
    support: Sequence[int],
    x: np.ndarray,
    c: float,
) -> np.ndarray:
    """Vector of invasion fitnesses (A x*)_k − c for k ∉ S, in index
    order of the outside types. Length = N − |S|; may be empty.
    """
    n = A.shape[0]
    in_support = np.zeros(n, dtype=bool)
    in_support[list(support)] = True
    outside = np.where(~in_support)[0]
    if outside.size == 0:
        return np.empty(0, dtype=float)
    return A[np.ix_(outside, list(support))] @ x - c

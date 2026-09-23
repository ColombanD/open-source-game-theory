"""Fixation probabilities in a frequency-dependent Moran process.

Two types in a population of `M`: `k` mutants of type `i`, `M − k` residents
of type `j`. Payoffs exclude self-interaction (an individual does not play
itself), so with `k` mutants present:

    pi_i(k) = [ (k − 1)·A[i,i] + (M − k)·A[i,j] ] / (M − 1)
    pi_j(k) = [ k·A[j,i] + (M − k − 1)·A[j,j] ] / (M − 1)

Fitness is exponential, `f = exp(beta · pi)`, which is the standard choice for
strong selection: it stays positive for any payoff (no need to shift the
matrix, unlike `1 − w + w·pi`) and `beta` sweeps cleanly from neutral drift
(`beta → 0`) to deterministic selection (`beta → ∞`).

The birth-death chain is one-dimensional, so fixation has a closed form:

    rho = 1 / ( 1 + Σ_{m=1}^{M-1} Π_{k=1}^{m} gamma_k ),   gamma_k = T⁻(k)/T⁺(k)

and with this update `gamma_k` reduces to `exp(−beta·(pi_i(k) − pi_j(k)))`.
Computed in log space: the products underflow to zero for even moderate
`beta·M`, which would silently turn a small fixation probability into exactly
zero and corrupt the stationary distribution downstream.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np  # type: ignore


@dataclass(frozen=True)
class FixationResult:
    """rho(i -> j) alongside the neutral benchmark it should be judged against."""

    rho: float                # P(one i mutant takes over a population of j)
    neutral: float            # 1/M — the same probability under no selection
    ratio: float              # rho / neutral: >1 favoured, <1 suppressed
    population: int
    beta: float

    @property
    def is_advantageous(self) -> bool:
        """Fixates more often than a neutral mutant would."""
        return self.rho > self.neutral


def payoff_pair(
    A: np.ndarray, i: int, j: int, k: int, M: int
) -> tuple[float, float]:
    """`(pi_i, pi_j)` with `k` mutants of `i` among `M − k` residents of `j`.

    Self-interaction is excluded, hence the `M − 1` denominator and the
    `k − 1` / `M − k − 1` counts: an individual meets everyone but itself.
    """
    if M < 2:
        raise ValueError(f"population must be at least 2, got {M}")
    denominator = M - 1
    pi_i = ((k - 1) * A[i, i] + (M - k) * A[i, j]) / denominator
    pi_j = (k * A[j, i] + (M - k - 1) * A[j, j]) / denominator
    return float(pi_i), float(pi_j)


def fixation_probability(
    A: np.ndarray, i: int, j: int, M: int, beta: float
) -> FixationResult:
    """Probability that ONE mutant of type `i` takes over a resident `j`.

    The sum is accumulated in log space. `gamma` products decay (or grow)
    exponentially in `beta·M`, so the naive product underflows to 0 or
    overflows to inf well within the parameter range this project sweeps —
    which would report a rare-but-possible fixation as impossible.
    """
    if M < 2:
        raise ValueError(f"population must be at least 2, got {M}")
    if i == j:
        # A type always "fixates" in itself; the question is degenerate.
        return FixationResult(1.0, 1.0 / M, M * (1.0 / M), M, beta)

    # log_prod[m] = Σ_{k=1..m} log gamma_k
    log_terms = []
    running = 0.0
    for k in range(1, M):
        pi_i, pi_j = payoff_pair(A, i, j, k, M)
        running += -beta * (pi_i - pi_j)
        log_terms.append(running)

    # rho = 1 / (1 + Σ exp(log_prod[m])), stabilised by factoring out the max.
    largest = max(log_terms)
    if largest > 700:  # exp overflows around 709
        # The suppressing terms dominate overwhelmingly: fixation is
        # effectively impossible. Report it as such rather than as inf/nan.
        total = float("inf")
    else:
        total = float(np.sum(np.exp(np.asarray(log_terms))))

    rho = 1.0 / (1.0 + total) if np.isfinite(total) else 0.0
    neutral = 1.0 / M
    return FixationResult(
        rho=rho,
        neutral=neutral,
        ratio=(rho / neutral) if neutral > 0 else float("nan"),
        population=M,
        beta=beta,
    )


def fixation_matrix(A: np.ndarray, M: int, beta: float) -> np.ndarray:
    """`R[i, j] = rho(i -> j)` for every ordered pair; diagonal set to 0.

    The diagonal is zeroed because these are TRANSITION rates for the
    small-mutation chain in `stationary.py`, where "fixating in yourself" is
    not a move.
    """
    n = A.shape[0]
    R = np.zeros((n, n), dtype=float)
    for i in range(n):
        for j in range(n):
            if i != j:
                R[i, j] = fixation_probability(A, i, j, M, beta).rho
    return R

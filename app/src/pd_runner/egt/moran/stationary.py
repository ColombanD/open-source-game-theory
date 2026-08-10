"""The small-mutation-limit stationary distribution, and stochastic stability.

When mutations are rare enough that each one fixates or dies out before the
next arrives, the population is a monoculture almost all of the time. Its
wandering between monocultures is then a Markov chain on the `N` types, with

    P[j -> i] = rho(i -> j) / (N − 1)     for i != j
    P[j -> j] = 1 − Σ_{i != j} P[j -> i]

(a mutant of a uniformly-chosen other type arrives, and fixates with
probability `rho`). Its stationary distribution is the fraction of TIME the
population spends as each type — the closest thing this project has to
"which equilibrium actually happens".

The types carrying the most mass are the STOCHASTICALLY STABLE ones. This can
disagree with every earlier stage: a type can be no ESS, sit in a cycle, and
still dominate the long run because it is hard to invade and easy to reach.
"""

from __future__ import annotations

from dataclasses import dataclass

import numpy as np  # type: ignore

from .process import fixation_matrix

# Mass above which a type counts as stochastically stable. Uniform mass is
# 1/N, so this is "carries at least half again the neutral share" — a
# threshold, deliberately reported alongside the raw distribution so a reader
# can apply their own.
_STABLE_MULTIPLE = 1.5


@dataclass
class MoranResult:
    """One `(M, beta)` point: fixation matrix, stationary distribution, verdict."""

    names: list[str]
    population: int
    beta: float
    fixation: np.ndarray          # R[i, j] = rho(i -> j)
    stationary: np.ndarray        # time share per type
    converged: bool               # the eigen-solve produced a valid distribution

    @property
    def neutral_share(self) -> float:
        return 1.0 / len(self.names)

    def stochastically_stable(self) -> list[str]:
        """Types carrying markedly more than the uniform share."""
        cut = _STABLE_MULTIPLE * self.neutral_share
        order = np.argsort(-self.stationary)
        return [self.names[i] for i in order if self.stationary[i] >= cut]

    def ranked(self) -> list[tuple[str, float]]:
        order = np.argsort(-self.stationary)
        return [(self.names[i], float(self.stationary[i])) for i in order]

    def summary(self) -> dict:
        return {
            "population": self.population,
            "beta": self.beta,
            "converged": self.converged,
            "neutral_share": round(self.neutral_share, 6),
            "stochastically_stable": self.stochastically_stable(),
            "stationary": [[n, round(p, 6)] for n, p in self.ranked()],
        }


def transition_matrix(fixation: np.ndarray) -> np.ndarray:
    """Small-mutation chain `P[j -> i]` from the fixation matrix."""
    n = fixation.shape[0]
    if n < 2:
        return np.ones((1, 1))
    P = np.zeros((n, n), dtype=float)
    for j in range(n):
        for i in range(n):
            if i != j:
                P[j, i] = fixation[i, j] / (n - 1)
        P[j, j] = 1.0 - P[j].sum()
    return P


def stationary_distribution(P: np.ndarray) -> tuple[np.ndarray, bool]:
    """Left eigenvector of `P` for eigenvalue 1, normalised to a distribution.

    Returns `(distribution, converged)`. `converged=False` means the solve did
    not yield a usable distribution (no eigenvalue near 1, or the result had
    no positive mass); the caller must not present the vector as a result.
    """
    n = P.shape[0]
    if n == 1:
        return np.ones(1), True

    values, vectors = np.linalg.eig(P.T)
    idx = int(np.argmin(np.abs(values - 1.0)))
    if abs(values[idx] - 1.0) > 1e-6:
        return np.full(n, 1.0 / n), False

    vector = np.real(vectors[:, idx])
    # An eigenvector is defined up to sign; the distribution is the
    # non-negative one.
    if vector.sum() < 0:
        vector = -vector
    vector = np.clip(vector, 0.0, None)
    total = vector.sum()
    if total <= 0:
        return np.full(n, 1.0 / n), False
    return vector / total, True


def analyse(
    A: np.ndarray, names: list[str], population: int, beta: float
) -> MoranResult:
    """Fixation matrix -> small-mutation chain -> stationary distribution."""
    n = len(names)
    if A.shape != (n, n):
        raise ValueError(f"A is {A.shape}, expected ({n}, {n})")

    fixation = fixation_matrix(A, population, beta)
    stationary, converged = stationary_distribution(transition_matrix(fixation))
    return MoranResult(
        names=list(names),
        population=population,
        beta=beta,
        fixation=fixation,
        stationary=stationary,
        converged=converged,
    )

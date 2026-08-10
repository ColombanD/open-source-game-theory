"""Stage (iv): the Moran process, fixation, and stochastic stability.

The strongest check available here is NEUTRAL DRIFT: at beta = 0 selection is
switched off, so a single mutant fixates with probability exactly 1/M for ANY
payoff matrix. That is a closed-form identity, and it pins the fixation
formula far more tightly than any simulation would.
"""

from __future__ import annotations

import numpy as np
import pytest

from pd_runner.egt.moran import (
    analyse,
    fixation_matrix,
    fixation_probability,
    payoff_pair,
)
from pd_runner.egt.moran.stationary import stationary_distribution, transition_matrix

PD = np.array([[2.0, -1.0], [3.0, 0.0]])          # D dominates C
COORDINATION = np.array([[2.0, 0.0], [0.0, 1.0]])  # two strict equilibria


# --------------------------------------------------------------------------
# Neutral drift — the analytic anchor
# --------------------------------------------------------------------------


@pytest.mark.parametrize("M", [2, 5, 10, 50, 100])
def test_neutral_fixation_is_exactly_one_over_M(M):
    """beta = 0 removes selection, so rho = 1/M whatever the payoffs are."""
    result = fixation_probability(PD, 0, 1, M=M, beta=0.0)
    assert result.rho == pytest.approx(1.0 / M, abs=1e-12)
    assert result.ratio == pytest.approx(1.0, abs=1e-9)


def test_neutral_drift_holds_for_an_arbitrary_matrix():
    rng = np.random.default_rng(4)
    A = rng.normal(size=(3, 3)) * 10
    for i, j in ((0, 1), (2, 0), (1, 2)):
        assert fixation_probability(A, i, j, M=25, beta=0.0).rho == pytest.approx(
            1 / 25, abs=1e-12)


# --------------------------------------------------------------------------
# Selection
# --------------------------------------------------------------------------


def test_dominated_strategy_is_suppressed_and_dominant_is_favoured():
    into_defectors = fixation_probability(PD, 0, 1, M=20, beta=1.0)
    into_cooperators = fixation_probability(PD, 1, 0, M=20, beta=1.0)
    assert not into_defectors.is_advantageous
    assert into_cooperators.is_advantageous
    assert into_defectors.rho < into_cooperators.rho


def test_tiny_fixation_probabilities_survive_the_arithmetic():
    """Log-space accumulation: the naive product underflows to exactly 0.

    A rare-but-possible fixation reported as impossible would silently
    corrupt the stationary distribution downstream.
    """
    result = fixation_probability(PD, 0, 1, M=40, beta=1.0)
    assert result.rho > 0.0
    assert result.rho < 1e-12


def test_stronger_selection_sharpens_the_advantage():
    weak = fixation_probability(PD, 1, 0, M=20, beta=0.05)
    strong = fixation_probability(PD, 1, 0, M=20, beta=1.0)
    assert strong.rho > weak.rho


def test_payoffs_exclude_self_interaction():
    """With k mutants of i, an individual meets M-1 others, not M."""
    A = np.array([[1.0, 2.0], [3.0, 4.0]])
    pi_i, pi_j = payoff_pair(A, 0, 1, k=1, M=5)
    # One mutant: it meets 0 of its own kind and all 4 residents.
    assert pi_i == pytest.approx((0 * 1.0 + 4 * 2.0) / 4)
    # A resident meets the 1 mutant and its 3 fellow residents.
    assert pi_j == pytest.approx((1 * 3.0 + 3 * 4.0) / 4)


def test_population_must_be_at_least_two():
    with pytest.raises(ValueError, match="at least 2"):
        fixation_probability(PD, 0, 1, M=1, beta=1.0)


# --------------------------------------------------------------------------
# The small-mutation chain
# --------------------------------------------------------------------------


def test_transition_matrix_rows_are_distributions():
    P = transition_matrix(fixation_matrix(PD, M=20, beta=1.0))
    assert np.allclose(P.sum(axis=1), 1.0)
    assert (P >= 0).all()


def test_fixation_matrix_has_a_zero_diagonal():
    """These are transition rates; fixating in yourself is not a move."""
    R = fixation_matrix(PD, M=20, beta=1.0)
    assert np.allclose(np.diag(R), 0.0)


def test_stationary_distribution_is_a_distribution():
    P = transition_matrix(fixation_matrix(COORDINATION, M=20, beta=1.0))
    pi, converged = stationary_distribution(P)
    assert converged
    assert pi.sum() == pytest.approx(1.0)
    assert (pi >= 0).all()


def test_stationary_distribution_is_stationary():
    """pi P = pi — the defining property, checked rather than assumed."""
    P = transition_matrix(fixation_matrix(COORDINATION, M=20, beta=1.0))
    pi, _ = stationary_distribution(P)
    assert np.allclose(pi @ P, pi, atol=1e-9)


def test_prisoners_dilemma_spends_its_time_defecting():
    result = analyse(PD, ["C", "D"], population=20, beta=1.0)
    assert result.converged
    assert result.stochastically_stable() == ["D"]
    assert dict(result.ranked())["D"] > 0.99


def test_risk_dominant_equilibrium_wins_the_long_run():
    """Coordination: (2,2) is payoff-dominant, and here also risk-dominant."""
    result = analyse(COORDINATION, ["A", "B"], population=30, beta=1.0)
    assert result.converged
    assert result.ranked()[0][0] == "A"


def test_neutral_selection_gives_the_uniform_distribution():
    """With no selection every type is equally likely — the sanity floor."""
    result = analyse(PD, ["C", "D"], population=20, beta=0.0)
    assert result.converged
    for _, share in result.ranked():
        assert share == pytest.approx(0.5, abs=1e-9)
    assert result.stochastically_stable() == []


def test_analyse_rejects_a_mismatched_matrix():
    with pytest.raises(ValueError, match="expected"):
        analyse(PD, ["A", "B", "C"], population=10, beta=1.0)

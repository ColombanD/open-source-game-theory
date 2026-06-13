"""Fitting tests: vertex recovery, interior points, off-hull, coincident rows."""

from __future__ import annotations

import itertools

import numpy as np
import pytest

from distillation.fitting import (
    FITTERS,
    fit_all,
    fit_l1,
    fit_l2,
    fit_linf,
    is_identified,
    profile_stats,
)

# A small reference library with affinely independent rows.
R_SIMPLE = np.array(
    [
        [1.0, 1.0, 0.0],  # bot 0
        [0.0, 1.0, 1.0],  # bot 1
        [0.0, 0.0, 0.0],  # bot 2
    ]
)


def fitted_point(R, x, fitter):
    return fitter(R, x).fitted


@pytest.mark.parametrize("metric,fitter", FITTERS.items())
@pytest.mark.parametrize("k", range(3))
def test_exact_vertex_recovery(metric, fitter, k):
    """x == r_k -> weight concentrated on bot k, residual ~ 0, fit == r_k."""
    x = R_SIMPLE[k].copy()
    result = fitter(R_SIMPLE, x)
    assert result.residual < 1e-6
    np.testing.assert_allclose(result.fitted, x, atol=1e-6)
    assert result.weights[k] > 1.0 - 1e-4


@pytest.mark.parametrize("metric,fitter", FITTERS.items())
def test_fit_stays_in_unit_box(metric, fitter):
    rng = np.random.default_rng(0)
    for _ in range(10):
        x = rng.random(3)
        result = fitter(R_SIMPLE, x)
        assert np.all(result.fitted >= -1e-9)
        assert np.all(result.fitted <= 1 + 1e-9)
        assert abs(result.weights.sum() - 1.0) < 1e-6
        assert np.all(result.weights >= -1e-9)


def test_interior_point_l2_l1():
    """x = 0.5 r_a + 0.5 r_b -> residual ~ 0 and mass on {a, b} (assert on fit)."""
    a, b = 0, 1
    x = 0.5 * R_SIMPLE[a] + 0.5 * R_SIMPLE[b]
    for fitter in (fit_l2, fit_l1):
        result = fitter(R_SIMPLE, x)
        assert result.residual < 1e-6
        # Weights may be non-unique in general; assert on the fitted point and
        # that no mass leaks onto the irrelevant bot.
        np.testing.assert_allclose(result.fitted, x, atol=1e-6)
        assert result.weights[2] < 1e-4


def test_off_hull_strictly_positive_residual():
    """An x outside conv{r_i} must have a strictly positive residual everywhere.

    Every row of R_SIMPLE has coordinate 0 in {0, 1} but the convex hull's first
    coordinate is at most 1; pushing x[0] above 1 is infeasible. Use x just
    outside: here all rows have first-coord in {0,1}, but x with a coordinate
    pattern unreachable by any mixture. We pick x = [1, 0, 1]: coord 1 needs
    weight only on bot 0 (gives [1,1,0]); reaching coord2=1 needs bot1, which
    forces coord1=1. The two demands conflict -> positive residual.
    """
    x = np.array([1.0, 0.0, 1.0])
    for fitter in FITTERS.values():
        result = fitter(R_SIMPLE, x)
        assert result.residual > 1e-6


def test_l2_residual_matches_direct_projection():
    """Sanity-check the L2 residual against a brute-force simplex search."""
    x = np.array([0.9, 0.1, 0.7])
    result = fit_l2(R_SIMPLE, x)

    # Brute-force: grid over the simplex, project x onto conv{r_i}.
    A = R_SIMPLE.T
    best = np.inf
    grid = np.linspace(0, 1, 101)
    for w0 in grid:
        for w1 in grid:
            if w0 + w1 > 1.0 + 1e-9:
                continue
            w = np.array([w0, w1, 1.0 - w0 - w1])
            best = min(best, np.linalg.norm(A @ w - x))
    assert result.residual <= best + 1e-3
    assert result.residual == pytest.approx(best, abs=2e-2)


def test_coincident_rows_not_identified():
    """Two identical rows -> fitted point unique, weights NOT identified."""
    R = np.array(
        [
            [1.0, 0.0, 1.0],  # bot 0
            [1.0, 0.0, 1.0],  # bot 1 == bot 0 (coincident)
            [0.0, 1.0, 0.0],  # bot 2
        ]
    )
    x = R[0].copy()  # the shared profile
    result = fit_l2(R, x)
    assert result.residual < 1e-6
    np.testing.assert_allclose(result.fitted, x, atol=1e-6)
    # Active rows include the two coincident bots -> not affinely independent.
    assert set(result.active) <= {0, 1}
    assert result.identified is False
    # The combined mass on the coincident pair is ~1, however it is split.
    assert result.weights[0] + result.weights[1] == pytest.approx(1.0, abs=1e-4)


def test_is_identified_basic():
    assert is_identified(R_SIMPLE, (0, 1, 2)) is True
    assert is_identified(R_SIMPLE, (0,)) is True
    R_dup = np.array([[1.0, 0.0], [1.0, 0.0]])
    assert is_identified(R_dup, (0, 1)) is False


def test_l1_l2_agree_on_realizable_point():
    """On a realizable point both metrics reach residual 0 and the same fit."""
    x = 0.3 * R_SIMPLE[0] + 0.7 * R_SIMPLE[2]
    r1, r2 = fit_l1(R_SIMPLE, x), fit_l2(R_SIMPLE, x)
    assert r1.residual < 1e-6 and r2.residual < 1e-6
    np.testing.assert_allclose(r1.fitted, r2.fitted, atol=1e-5)


def test_profile_stats():
    x = np.array([1.0, 0.0, 0.5, 1.0])
    stats = profile_stats(x)
    assert stats["level"] == pytest.approx(0.625)
    assert stats["sharpness"] == pytest.approx((0.5 + 0.5 + 0.0 + 0.5) / 4)


def test_fit_all_runs_every_metric():
    x = np.array([0.4, 0.6, 0.2])
    results = fit_all(R_SIMPLE, x)
    assert [r.metric for r in results] == list(FITTERS)

"""Stage (iii): replicator dynamics and basins of attraction.

Validated against textbook games with known closed-form answers, in the same
spirit as the ported stages' tests — the OSGT matrix is the subject, not the
oracle.
"""

from __future__ import annotations

import numpy as np
import pytest

from pd_runner.egt.replicator import (
    estimate_basins,
    integrate,
    replicator_field,
    simplex_samples,
)

# Hawk-Dove with V=2, C=4: unique interior ESS at x_H = V/C = 1/2.
HAWK_DOVE = np.array([[(2 - 4) / 2, 2.0], [0.0, 2 / 2]])
# Prisoner's Dilemma: D strictly dominates C.
PD = np.array([[2.0, -1.0], [3.0, 0.0]])
# Rock-paper-scissors: zero-sum, closed orbits, nothing converges.
RPS = np.array([[0.0, -1.0, 1.0], [1.0, 0.0, -1.0], [-1.0, 1.0, 0.0]])


# --------------------------------------------------------------------------
# The field and the invariants that make integration meaningful
# --------------------------------------------------------------------------


def test_simplex_is_invariant():
    """Σ ẋ = 0, so the proportions keep summing to 1."""
    rng = np.random.default_rng(0)
    for _ in range(20):
        x = rng.dirichlet(np.ones(4))
        assert abs(replicator_field(rng.normal(size=(4, 4)), x).sum()) < 1e-12


def test_faces_are_invariant():
    """An absent type never appears: x_i = 0 implies ẋ_i = 0.

    Selection alone introduces nothing — that is what the Moran stage's
    mutation is for. A solver that violated this would invent types.
    """
    x = np.array([0.5, 0.5, 0.0])
    assert replicator_field(RPS, x)[2] == 0.0


def test_a_fixed_point_does_not_move():
    """The uniform mix of RPS is a rest point of the dynamics."""
    third = np.full(3, 1 / 3)
    assert np.max(np.abs(replicator_field(RPS, third))) < 1e-15


def test_trajectories_stay_on_the_simplex():
    traj = integrate(HAWK_DOVE, np.array([0.9, 0.1]))
    assert abs(traj.x.sum() - 1.0) < 1e-9
    assert (traj.x >= 0).all()


# --------------------------------------------------------------------------
# Known answers
# --------------------------------------------------------------------------


def test_hawk_dove_converges_to_v_over_c():
    """Every interior start reaches x_H = V/C = 0.5."""
    traj = integrate(HAWK_DOVE, np.array([0.9, 0.1]))
    assert traj.converged
    assert traj.x[0] == pytest.approx(0.5, abs=1e-4)


def test_hawk_dove_interior_basin_is_everything():
    result = estimate_basins(HAWK_DOVE, ["H", "D"], n_samples=40, seed=1)
    mixed = [a for a in result.attractors if not a.is_monoculture]
    assert len(mixed) == 1
    assert result.basin_fraction(mixed[0]) == pytest.approx(1.0)
    assert result.n_unconverged == 0


def test_prisoners_dilemma_collapses_to_defection():
    result = estimate_basins(PD, ["C", "D"], n_samples=40, seed=1)
    defect = next(a for a in result.attractors if a.support(["C", "D"]) == ["D"])
    assert result.basin_fraction(defect) == pytest.approx(1.0)


def test_monocultures_are_fixed_points_with_no_basin():
    """all-C is a rest point of the PD, but nothing flows to it.

    This is the ESS-vs-reachability distinction the stage exists to draw: a
    fixed point can be unreachable from anywhere but itself.
    """
    result = estimate_basins(PD, ["C", "D"], n_samples=40, seed=1)
    coop = next(a for a in result.attractors if a.support(["C", "D"]) == ["C"])
    assert coop.n_interior == 0
    assert coop.vertex_sources == ["C"]


# --------------------------------------------------------------------------
# Non-convergence is a finding, not a failure
# --------------------------------------------------------------------------


def test_cyclic_games_are_reported_as_unconverged():
    """RPS orbits forever; endpoints must NOT be passed off as attractors."""
    result = estimate_basins(RPS, ["R", "P", "S"], n_samples=20, seed=1,
                             max_steps=5_000)
    assert result.n_unconverged > 0
    assert not result.all_converged
    # The vertices are genuine rest points and still resolve.
    assert any(a.is_monoculture for a in result.attractors)


def test_unconverged_runs_are_excluded_from_basin_denominators():
    result = estimate_basins(RPS, ["R", "P", "S"], n_samples=20, seed=1,
                             max_steps=5_000)
    assigned = sum(a.n_interior for a in result.attractors)
    assert assigned == result.n_interior_converged
    assert result.n_interior_converged <= result.n_interior_samples


# --------------------------------------------------------------------------
# Grouping by support
# --------------------------------------------------------------------------


def test_endpoints_are_grouped_by_support_not_proximity():
    """A continuum of rest points is ONE answer, not one per sample.

    On the real zoo the endpoints spread across a face (spread ≈ 0.5) while
    sharing a support. Grouping by proximity would report a separate attractor
    per sample, each with a tiny basin — arithmetically true, and a complete
    misreading of the dynamics.
    """
    result = estimate_basins(HAWK_DOVE, ["H", "D"], n_samples=40, seed=1)
    # Hawk-Dove has a genuine point attractor, so its spread is ~0.
    mixed = next(a for a in result.attractors if not a.is_monoculture)
    assert mixed.spread < 1e-3
    assert mixed.n_interior > 1


def test_support_excludes_dying_residue():
    """A type at 1e-9 is a numerical residue, not a member of the mixture."""
    result = estimate_basins(PD, ["C", "D"], n_samples=10, seed=1)
    defect = next(a for a in result.attractors if a.n_interior > 0)
    assert defect.support(["C", "D"]) == ["D"]


# --------------------------------------------------------------------------
# Sampling
# --------------------------------------------------------------------------


def test_interior_sampling_is_uniform_on_the_simplex():
    """Dirichlet(1), not normalised uniforms — the latter clump at the centre.

    A biased sampler would tilt every basin estimate toward whatever the
    centre flows to, which is exactly the number this stage reports.
    """
    xs = simplex_samples(3, 4000, seed=3, include_vertices=False,
                         include_uniform=False)
    assert np.allclose(xs.sum(axis=1), 1.0)
    # Under Dirichlet(1) each coordinate is Beta(1, 2): mean 1/3, and
    # P(x_0 > 0.5) = (1 - 0.5)^2 = 0.25.
    assert xs[:, 0].mean() == pytest.approx(1 / 3, abs=0.02)
    assert (xs[:, 0] > 0.5).mean() == pytest.approx(0.25, abs=0.03)


def test_vertices_are_included_and_separable():
    xs = simplex_samples(4, 0, seed=1, include_vertices=True,
                         include_uniform=False)
    assert xs.shape == (4, 4)
    assert np.array_equal(xs, np.eye(4))


def test_estimate_basins_rejects_a_mismatched_matrix():
    with pytest.raises(ValueError, match="expected"):
        estimate_basins(HAWK_DOVE, ["A", "B", "C"], n_samples=1)

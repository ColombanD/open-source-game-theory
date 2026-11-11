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
    second_order_invaders,
    simplex_samples,
)

# Hawk-Dove with V=2, C=4: unique interior ESS at x_H = V/C = 1/2.
HAWK_DOVE = np.array([[(2 - 4) / 2, 2.0], [0.0, 2 / 2]])
# Prisoner's Dilemma: D strictly dominates C.
PD = np.array([[2.0, -1.0], [3.0, 0.0]])
# Rock-paper-scissors: zero-sum, closed orbits, nothing converges.
RPS = np.array([[0.0, -1.0, 1.0], [1.0, 0.0, -1.0], [-1.0, 1.0, 0.0]])
# Rock-paper-scissors with a loss costing more than a win earns: the interior
# rest point is unstable and every orbit spirals out to the HETEROCLINIC cycle
# R -> P -> S -> R, slowing down near each corner without ever stopping.
RPS_BAD = np.array([[0.0, -2.0, 1.0], [1.0, 0.0, -2.0], [-2.0, 1.0, 0.0]])
# Zero-sum rock-paper-scissors with unequal stakes: closed orbits around the
# interior rest point (1/4, 1/2, 1/4), so the uniform mix is NOT at rest.
RPS_BIASED = np.array([[0.0, -1.0, 2.0], [1.0, 0.0, -1.0], [-2.0, 1.0, 0.0]])
# A neutral type that earns more against itself: type 1 ties type 0 against a
# population of 0s and gets 2 against its own kind, so it invades at SECOND
# order, like DupocBot invading full defection.
SLOW_INVASION = np.array([[0.0, 0.0], [0.0, 2.0]])


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
                             max_rhs_evals=5_000)
    assert result.n_unconverged > 0
    assert not result.all_converged
    # Closed orbits cost the solver evaluations forever: they exhaust the budget.
    assert result.n_budget_exhausted > 0
    # The vertices are genuine rest points and still resolve.
    assert any(a.is_monoculture for a in result.attractors)


def test_a_cycling_game_stops_after_the_probe():
    """Half or more of the first starts exhaust their budget: the rest are not integrated."""
    probe = estimate_basins(RPS_BIASED, ["R", "P", "S"], n_samples=40, seed=1,
                            max_rhs_evals=2_000, cycle_probe=10)
    assert probe.truncated_cycling
    assert probe.n_interior_samples == 10 and probe.n_interior_requested == 41
    assert probe.n_budget_exhausted == 10
    assert probe.summary()["truncated_cycling"] is True
    # Basins stay shares of the starts integrated, so they still add up to 1.
    total = sum(probe.basin_fraction(a) for a in probe.attractors)
    assert total + probe.unconverged_fraction == pytest.approx(1.0)


def test_the_probe_counts_a_start_that_settles():
    """In RPS the uniform start sits on the rest point and converges; the other nine cycle.

    The game is still cut at the probe, and the one converged start keeps its basin.
    """
    result = estimate_basins(RPS, ["R", "P", "S"], n_samples=40, seed=1,
                             max_rhs_evals=2_000, cycle_probe=10)
    assert result.truncated_cycling and result.n_interior_samples == 10
    assert result.n_interior_converged == 1 and result.n_budget_exhausted == 9


def test_a_settling_game_is_never_cut():
    result = estimate_basins(HAWK_DOVE, ["H", "D"], n_samples=40, seed=1, cycle_probe=10)
    assert not result.truncated_cycling and result.n_interior_samples == 41


def test_a_heteroclinic_cycle_is_not_convergence():
    """Slow is not settled: near each corner the speed vanishes, the path does not stop.

    The speed test `max|xdot| < 1e-7` (until 2026-11-10) passed near every
    corner and reported all 51 starts as converged to a monoculture. Only the
    uniform mix, which IS the interior rest point, converges.
    """
    result = estimate_basins(RPS_BAD, ["R", "P", "S"], n_samples=20, seed=1,
                             max_horizon=1e5)
    assert result.n_interior_converged == 1          # the uniform start, exactly at rest
    assert result.n_unconverged == 20
    assert not any(a.is_monoculture and a.n_interior for a in result.attractors)


def test_basins_are_shares_of_all_interior_starts():
    """Unconverged starts are their own share: basins + unconverged = 1."""
    result = estimate_basins(RPS, ["R", "P", "S"], n_samples=20, seed=1,
                             max_rhs_evals=5_000)
    assigned = sum(a.n_interior for a in result.attractors)
    assert assigned == result.n_interior_converged
    assert result.n_interior_converged <= result.n_interior_samples
    total = sum(result.basin_fraction(a) for a in result.attractors)
    assert total + result.unconverged_fraction == pytest.approx(1.0)


# --------------------------------------------------------------------------
# A second-order invasion: converged within tolerance is not an attractor
# --------------------------------------------------------------------------


def test_second_order_invader_is_detected():
    """Type 1 ties at all-0 and earns more against itself: it invades, slowly."""
    assert second_order_invaders(SLOW_INVASION, np.array([1.0, 0.0])) == (1,)
    # All-1 is strict: nothing invades it.
    assert second_order_invaders(SLOW_INVASION, np.array([0.0, 1.0])) == ()
    # In the PD, C does not even tie at all-D: not an invader.
    assert second_order_invaders(PD, np.array([0.0, 1.0])) == ()


def test_a_tied_type_caught_just_above_the_absent_cut_is_still_an_invader():
    """At a share of 2e-6 the invader is "present" (>= 1e-6) but on its way up, not settled."""
    weak = np.array([[0.0, 0.0], [0.0, 0.2]])   # growth 0.2·x: still "tied" (< 1e-6) at x = 2e-6
    assert second_order_invaders(weak, np.array([1 - 2e-6, 2e-6])) == (1,)
    # A small member of a NEUTRAL mixture has a zero second-order coefficient: not an invader.
    neutral = np.array([[2.0, 2.0], [2.0, 2.0]])
    assert second_order_invaders(neutral, np.array([1 - 2e-6, 2e-6])) == ()


def test_a_slow_invasion_escapes_given_the_time():
    """From a share of 1e-4 the invader needs ~1/(2·1e-4) = 5000 time units, and gets there."""
    traj = integrate(SLOW_INVASION, np.array([1 - 1e-4, 1e-4]))
    assert traj.converged and not traj.metastable
    assert traj.x[1] == pytest.approx(1.0, abs=1e-6)


def test_a_slower_invasion_than_the_horizon_is_flagged_metastable():
    """From 1e-12 the escape takes ~5e11: at horizon 1e9 the start sits at all-0, FLAGGED.

    It is a Nash equilibrium up to tolerance, so it counts as converged — but
    the exact dynamics leaves it, and the trajectory says so instead of
    reporting an attractor.
    """
    traj = integrate(SLOW_INVASION, np.array([1 - 1e-12, 1e-12]))
    assert traj.converged and traj.metastable
    assert traj.second_order_invaders == (1,)
    assert traj.horizon == 1e9             # integrated on to the last horizon
    assert traj.x[0] == pytest.approx(1.0, abs=1e-6)


def test_metastable_basins_are_flagged_in_the_summary():
    result = estimate_basins(SLOW_INVASION, ["stay", "invade"], n_samples=30, seed=1)
    # Interior Dirichlet starts all have a sizeable invader share: they escape.
    invaded = next(a for a in result.attractors if a.support(result.names) == ["invade"])
    assert result.basin_fraction(invaded) == pytest.approx(1.0)
    assert result.n_metastable == 0
    assert all(not a["metastable"] for a in result.summary()["attractors"])


# --------------------------------------------------------------------------
# Matching endpoints to Nash components
# --------------------------------------------------------------------------


def test_endpoints_are_matched_to_nash_components():
    """Two payoff-identical cooperators and a dominated defector: one continuum, one component.

    Types 0 and 1 earn 2 with each other and with themselves; type 2 earns 0
    against everyone. Every mix of 0 and 1 is a rest point, so the endpoints
    spread over SEVERAL supports but ONE Nash component.
    """
    from fractions import Fraction as F

    A = np.array([[2.0, 2.0, 2.0], [2.0, 2.0, 2.0], [0.0, 0.0, 0.0]])
    e0, e1 = (F(1), F(0), F(0)), (F(0), F(1), F(0))
    equilibria = [(e0, e0, 0), (e0, e1, 0), (e1, e0, 0), (e1, e1, 0)]
    result = estimate_basins(A, ["a", "b", "d"], n_samples=30, seed=1, equilibria=equilibria)
    assert result.all_converged and result.n_unlocated == 0
    (component,) = result.component_basins()
    assert component["component_id"] == 0
    assert component["basin_fraction"] == pytest.approx(1.0)
    assert component["bots"] == ["a", "b"]


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

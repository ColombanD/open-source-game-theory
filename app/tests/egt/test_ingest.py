"""The ingest seam: action-pair cells -> payoff matrix A.

Replaces the standalone repo's `test_payoffs.py` (PD-parameter validation,
kept below) and rebases the two `test_invasion_io.py` tests that drove the
deleted CSV+config path.
"""

from __future__ import annotations

import numpy as np
import pytest

from pd_runner.egt.ingest import (
    UndefinedPayoffError,
    payoff_matrix_from_cells,
    payoff_matrix_from_tau_matrix,
    payoff_matrix_from_tournament,
    row_payoff,
    validate_pd_params,
)

B, C = 3.0, 1.0


# --------------------------------------------------------------------------
# PD convention (ported from the standalone test_payoffs.py)
# --------------------------------------------------------------------------


def test_validate_pd_params_accepts_b_gt_c_gt_0():
    validate_pd_params(3.0, 1.0)


@pytest.mark.parametrize("b,c", [(1.0, 1.0), (0.5, 1.0), (3.0, 0.0), (3.0, -1.0)])
def test_validate_pd_params_rejects_non_pd(b, c):
    with pytest.raises(ValueError):
        validate_pd_params(b, c)


def test_row_payoff_orders_T_R_P_S():
    T = row_payoff(("D", "C"), B, C)
    R = row_payoff(("C", "C"), B, C)
    P = row_payoff(("D", "D"), B, C)
    S = row_payoff(("C", "D"), B, C)
    assert T > R > P > S


def test_row_payoff_rejects_non_terminating_cell():
    with pytest.raises(UndefinedPayoffError):
        row_payoff(("N", "N"), B, C)


# --------------------------------------------------------------------------
# cells -> A
# --------------------------------------------------------------------------


def _two_bot_cells():
    return {
        ("Coop", "Coop"): ("C", "C"),
        ("Coop", "Defect"): ("C", "D"),
        ("Defect", "Coop"): ("D", "C"),
        ("Defect", "Defect"): ("D", "D"),
    }


def test_payoff_matrix_from_cells_is_the_pd():
    pm = payoff_matrix_from_cells(("Coop", "Defect"), _two_bot_cells(), b=B, c=C)
    assert pm.bots == ("Coop", "Defect")
    np.testing.assert_array_equal(pm.A, np.array([[2.0, -1.0], [3.0, 0.0]]))
    assert pm.is_fully_proven


def test_row_and_column_roles_are_not_transposed():
    """A[i, j] is the ROW player's payoff — the asymmetry must survive."""
    pm = payoff_matrix_from_cells(("Coop", "Defect"), _two_bot_cells(), b=B, c=C)
    i, j = pm.bots.index("Coop"), pm.bots.index("Defect")
    assert pm.A[i, j] == -C   # Coop meets Defect: the sucker payoff
    assert pm.A[j, i] == B    # Defect meets Coop: the temptation payoff


def test_missing_cell_raises_rather_than_imputing():
    cells = _two_bot_cells()
    del cells[("Coop", "Defect")]
    with pytest.raises(UndefinedPayoffError, match="missing cell"):
        payoff_matrix_from_cells(("Coop", "Defect"), cells, b=B, c=C)


# --------------------------------------------------------------------------
# the "N" (proven non-termination) state
# --------------------------------------------------------------------------


def _cells_with_n():
    cells = _two_bot_cells()
    cells.update({
        ("Mirror", "Mirror"): ("N", "N"),
        ("Mirror", "Coop"): ("C", "C"),
        ("Coop", "Mirror"): ("C", "C"),
        ("Mirror", "Defect"): ("D", "D"),
        ("Defect", "Mirror"): ("D", "D"),
    })
    return cells


def test_exclude_policy_drops_non_terminating_bot():
    pm = payoff_matrix_from_cells(
        ("Coop", "Defect", "Mirror"), _cells_with_n(), b=B, c=C,
        non_termination="exclude",
    )
    assert pm.excluded_bots == ("Mirror",)
    assert pm.bots == ("Coop", "Defect")
    assert pm.A.shape == (2, 2)


def test_payoff_policy_keeps_bot_and_records_the_number():
    pm = payoff_matrix_from_cells(
        ("Coop", "Defect", "Mirror"), _cells_with_n(), b=B, c=C,
        non_termination="payoff", non_termination_payoff=0.0,
    )
    assert pm.excluded_bots == ()
    assert pm.bots == ("Coop", "Defect", "Mirror")
    k = pm.bots.index("Mirror")
    assert pm.A[k, k] == 0.0
    assert pm.assumptions()["non_termination"]["payoff"] == 0.0


def test_payoff_policy_requires_an_explicit_number():
    """A non-termination payoff must be chosen, never defaulted."""
    with pytest.raises(ValueError, match="explicit non_termination_payoff"):
        payoff_matrix_from_cells(
            ("Coop", "Defect", "Mirror"), _cells_with_n(), b=B, c=C,
            non_termination="payoff",
        )


# --------------------------------------------------------------------------
# provenance
# --------------------------------------------------------------------------


def test_assumptions_records_the_convention_and_policy():
    pm = payoff_matrix_from_cells(
        ("Coop", "Defect"), _two_bot_cells(), b=B, c=C, zoo="test", t=0.5, alpha=0.7,
    )
    a = pm.assumptions()
    trps = a["pd_payoffs"]["implied_trps"]
    assert trps["T"] > trps["R"] > trps["P"] > trps["S"]
    assert a["tau"] == {"t": 0.5, "alpha": 0.7}
    assert a["zoo"] == "test"
    assert a["n_types"] == 2


def test_stipulated_cells_make_the_matrix_conditional():
    pm = payoff_matrix_from_cells(
        ("Coop", "Defect"), _two_bot_cells(), b=B, c=C,
        stipulated_cells=[("Coop", "Defect")],
    )
    assert not pm.is_fully_proven
    assert pm.assumptions()["is_fully_proven"] is False


def test_stipulations_for_excluded_bots_are_dropped():
    """A stipulation naming a dropped bot must not linger in the provenance."""
    pm = payoff_matrix_from_cells(
        ("Coop", "Defect", "Mirror"), _cells_with_n(), b=B, c=C,
        non_termination="exclude", stipulated_cells=[("Mirror", "Coop")],
    )
    assert pm.excluded_bots == ("Mirror",)
    assert pm.stipulated_cells == ()


# --------------------------------------------------------------------------
# the real zoos (rebased from the standalone test_osgt_regression)
# --------------------------------------------------------------------------


@pytest.mark.parametrize("zoo_key", ["default", "enlarged"])
def test_real_zoo_builds_a_total_payoff_matrix(zoo_key):
    from pd_runner.tau.matrix import get_zoo

    named = get_zoo(zoo_key)
    pm = payoff_matrix_from_tau_matrix(named.load(), zoo=zoo_key)

    assert pm.A.shape == (len(pm.bots), len(pm.bots))
    assert np.isfinite(pm.A).all()
    # Every entry is one of the four PD payoffs.
    assert set(np.unique(pm.A)) <= {B - C, -C, 0.0, B}


def test_enlarged_zoo_excludes_mirrorbot_for_non_termination():
    """MirrorBot self-play is a proven `none`; the default policy drops it."""
    from pd_runner.tau.matrix import get_zoo

    pm = payoff_matrix_from_tau_matrix(get_zoo("enlarged").load(), zoo="enlarged")
    assert "MirrorBot" in pm.excluded_bots
    assert "MirrorBot" not in pm.bots


def test_tau_anchor_theorem_at_full_transparency():
    """At t=1 the tau tournament reproduces the base matrix exactly.

    This is the anchor theorem, and it doubles as an orientation check on the
    ingest seam: a transposed or mis-indexed A would not match.
    """
    from pd_runner.tau.matrix import get_zoo
    from pd_runner.tau.sweep import run_tournament

    m = get_zoo("default").load()
    base = payoff_matrix_from_tau_matrix(m, zoo="default")

    for alpha in (0.3, 0.8):
        result = run_tournament(m, t=1.0, alpha=alpha)
        lifted = payoff_matrix_from_tournament(result, bots=m.bots, zoo="default")
        np.testing.assert_array_equal(lifted.A, base.A)


def test_tournament_matrix_carries_its_t_and_alpha():
    from pd_runner.tau.matrix import get_zoo
    from pd_runner.tau.sweep import run_tournament

    m = get_zoo("default").load()
    result = run_tournament(m, t=0.5, alpha=0.62)
    pm = payoff_matrix_from_tournament(result, bots=m.bots, zoo="default")

    assert pm.t == 0.5 and pm.alpha == 0.62
    assert pm.assumptions()["tau"] == {"t": 0.5, "alpha": 0.62}


def test_bot_order_is_recovered_when_not_given():
    from pd_runner.tau.matrix import get_zoo
    from pd_runner.tau.sweep import run_tournament

    m = get_zoo("default").load()
    result = run_tournament(m, t=0.5, alpha=0.5)
    assert payoff_matrix_from_tournament(result).bots == tuple(m.bots)

"""3x3 engineered so the full-support algebraic solution has a negative
component: row recorded with is_interior=False, overall_class='non_interior',
eigvals are NOT computed.

Construction: pick x* = (-0.5, 0.7, 0.8) (sum = 1.0) and choose
A = diag(-2, 10/7, 5/4). Then A @ x* = (1, 1, 1) so the block system
solves to that x* with c = 1. The matrix is non-singular (diagonal
entries are non-zero).
"""

from __future__ import annotations

import math

import numpy as np

from src.faces.classify import build_row


def test_non_interior_full_support_recorded():
    A = np.diag([-2.0, 10.0 / 7.0, 5.0 / 4.0])
    names = ["X", "Y", "Z"]
    tol = 1e-10

    row = build_row(support_id=0, support=(0, 1, 2), names=names, A=A, tol=tol)

    assert row["is_singular"] is False
    assert row["is_interior"] is False

    # The algebraic x* still gets recorded (only singular rows get NaN xs)
    assert abs(row["x_X"] - (-0.5)) < 1e-12
    assert abs(row["x_Y"] - 0.7) < 1e-12
    assert abs(row["x_Z"] - 0.8) < 1e-12

    # Eigvals are NOT computed for non-interior solutions
    assert row["tangent_eigvals"] == "[]"
    assert math.isnan(row["max_re_eigval"])
    assert math.isnan(row["min_re_eigval"])
    assert row["has_complex_eigvals"] is False
    assert row["within_face_class"] == ""

    # External invasion fitnesses are also not computed
    assert row["external_invasion_fitnesses"] == "{}"
    assert row["max_external_fitness"] == float("-inf")
    assert row["externally_stable"] is True

    assert row["overall_class"] == "non_interior"

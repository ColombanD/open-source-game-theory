"""Singular A_SS on a 2x2 sub-face: row recorded with is_singular=True,
NaN equilibrium columns, overall_class='singular'.
"""

from __future__ import annotations

import math

import numpy as np

from src.faces.classify import build_row


def test_singular_2x2_face_recorded_not_skipped():
    A = np.array([[1.0, 1.0], [1.0, 1.0]])
    names = ["X", "Y"]
    tol = 1e-10

    row = build_row(support_id=0, support=(0, 1), names=names, A=A, tol=tol)

    assert row["is_singular"] is True
    assert row["is_interior"] is False
    assert math.isnan(row["x_X"])
    assert math.isnan(row["x_Y"])
    assert math.isnan(row["c"])
    assert math.isnan(row["c_crosscheck"])
    assert row["tangent_eigvals"] == "[]"
    assert math.isnan(row["max_re_eigval"])
    assert math.isnan(row["min_re_eigval"])
    assert row["has_complex_eigvals"] is False
    assert row["within_face_class"] == ""
    assert row["overall_class"] == "singular"

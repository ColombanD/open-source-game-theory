"""Rock-paper-scissors (3x3, zero-sum): full-support equilibrium is
(1/3, 1/3, 1/3) with purely imaginary tangent eigenvalues
±i/sqrt(3); the row should be classified as non_hyperbolic.
"""

from __future__ import annotations

import json
import math

import numpy as np

from src.faces.classify import build_row


def test_rps_full_support_non_hyperbolic():
    A = np.array(
        [[0.0, -1.0, 1.0], [1.0, 0.0, -1.0], [-1.0, 1.0, 0.0]]
    )
    names = ["R", "P", "S"]
    tol = 1e-10

    row = build_row(support_id=0, support=(0, 1, 2), names=names, A=A, tol=tol)

    assert row["is_interior"] is True
    assert row["is_singular"] is False
    assert abs(row["x_R"] - 1 / 3) < 1e-12
    assert abs(row["x_P"] - 1 / 3) < 1e-12
    assert abs(row["x_S"] - 1 / 3) < 1e-12
    assert abs(row["c"]) < 1e-12
    assert abs(row["c_crosscheck"]) < 1e-12

    eigs = json.loads(row["tangent_eigvals"])
    assert len(eigs) == 2  # |S|-1
    # Both real parts ~ 0, imaginary parts ~ ±1/sqrt(3)
    expected_im = 1.0 / math.sqrt(3.0)
    for re, _im in eigs:
        assert abs(re) < 1e-8
    ims = sorted([im for _re, im in eigs])
    assert abs(ims[0] - (-expected_im)) < 1e-8
    assert abs(ims[1] - expected_im) < 1e-8

    assert row["has_complex_eigvals"] is True
    assert row["within_face_class"] == "non_hyperbolic"

    # full support => external stability vacuous
    assert row["external_invasion_fitnesses"] == "{}"
    assert row["max_external_fitness"] == float("-inf")
    assert row["externally_stable"] is True

    assert row["overall_class"] == "non_hyperbolic"

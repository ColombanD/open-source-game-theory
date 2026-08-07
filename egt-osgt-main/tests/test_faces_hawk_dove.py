"""Hawk-Dove (2x2): full-support row should be asymptotically stable
with x_H* = V/C and a single (1-D tangent) eigenvalue with Re<0.
External stability is vacuous on the full simplex (max_external_fitness
= -inf, externally_stable = True).
"""

from __future__ import annotations

import json

import numpy as np

from src.faces.classify import build_row


def test_hawk_dove_full_support_asymp_stable():
    V, C = 2.0, 4.0
    A = np.array([[(V - C) / 2.0, V], [0.0, V / 2.0]])
    names = ["H", "D"]
    tol = 1e-10

    row = build_row(support_id=0, support=(0, 1), names=names, A=A, tol=tol)

    assert row["is_interior"] is True
    assert row["is_singular"] is False
    assert row["support_mask"] == "11"
    assert row["support_tuple"] == "(H, D)"

    # x_H* = V/C
    assert row["x_H"] == 0.5
    assert row["x_D"] == 0.5

    # c and crosscheck agree
    assert abs(row["c"] - row["c_crosscheck"]) < 1e-9

    # 1-D tangent space => exactly one eigenvalue
    eigs = json.loads(row["tangent_eigvals"])
    assert len(eigs) == 1
    re, im = eigs[0]
    assert re < -1e-9
    assert abs(im) < tol

    assert row["within_face_class"] == "asymptotically_stable"
    assert row["max_re_eigval"] < -1e-9
    assert row["min_re_eigval"] < -1e-9
    assert row["has_complex_eigvals"] is False

    # full support => external stability is vacuous
    assert row["external_invasion_fitnesses"] == "{}"
    assert row["max_external_fitness"] == float("-inf")
    assert row["externally_stable"] is True

    assert row["overall_class"] == "asymp_stable"

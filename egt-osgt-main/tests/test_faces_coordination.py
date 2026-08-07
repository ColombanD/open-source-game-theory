"""3x3 coordination game A = diag(1, 1, 1):
    * 2-face equilibria at (1/2, 1/2) are interior, with a single
      positive tangent eigenvalue → 'unstable'.
    * 3-face interior at (1/3, 1/3, 1/3) likewise has positive real
      parts → 'unstable'.
"""

from __future__ import annotations

import numpy as np

from src.faces.classify import build_row
from src.faces.enumerate import enumerate_supports


def test_coordination_all_supports_unstable():
    A = np.eye(3)
    names = ["A", "B", "C"]
    tol = 1e-10

    rows = []
    for sid, support in enumerate(enumerate_supports(3)):
        rows.append(build_row(sid, support, names, A, tol))

    # |S|=2 sub-faces: x* = (1/2, 1/2), unstable
    sub2 = [r for r in rows if r["support_size"] == 2]
    assert len(sub2) == 3
    for r in sub2:
        assert r["is_interior"] is True
        assert r["overall_class"] == "unstable"
        assert r["within_face_class"] == "unstable"

    # |S|=3 face: x* = (1/3,1/3,1/3), positive eigvals → unstable
    sub3 = [r for r in rows if r["support_size"] == 3]
    assert len(sub3) == 1
    r = sub3[0]
    assert r["is_interior"] is True
    assert abs(r["x_A"] - 1 / 3) < 1e-12
    assert abs(r["x_B"] - 1 / 3) < 1e-12
    assert abs(r["x_C"] - 1 / 3) < 1e-12
    assert r["within_face_class"] == "unstable"
    # external stability vacuous on full support
    assert r["externally_stable"] is True
    assert r["overall_class"] == "unstable"

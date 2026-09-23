"""Classification and per-row assembly for face-equilibrium analysis.

Within-face stability is read off the tangent-space eigenvalues; external
stability is read off the invasion-fitness vector against types outside
S. The overall class is a single categorical column for quick filtering.
"""

from __future__ import annotations

import json
import math
from typing import Dict, Optional, Sequence

import numpy as np  # type: ignore

from .enumerate import support_bitmask, support_tuple_str
from .jacobian import (
    FaceSolution,
    external_invasion_fitness,
    replicator_jacobian,
    solve_face,
    tangent_eigvals,
)


def classify_within_face(eigs: np.ndarray, tol: float) -> Dict[str, object]:
    """Categorise an interior face equilibrium from its tangent eigvals.

    Keys returned: within_face_class, max_re_eigval, min_re_eigval,
    has_complex_eigvals, tangent_eigvals_json.
    """
    re = eigs.real
    im = eigs.imag
    max_re = float(re.max())
    min_re = float(re.min())
    has_complex = bool(np.any(np.abs(im) > tol))

    if np.any(np.abs(re) <= tol):
        cls = "non_hyperbolic"
    elif max_re < -tol:
        cls = "asymptotically_stable"
    elif min_re > tol:
        cls = "unstable"
    else:
        cls = "saddle"

    eig_pairs = [[float(z.real), float(z.imag)] for z in eigs]
    return {
        "within_face_class": cls,
        "max_re_eigval": max_re,
        "min_re_eigval": min_re,
        "has_complex_eigvals": has_complex,
        "tangent_eigvals": json.dumps(eig_pairs),
    }


def classify_overall(
    is_singular: bool,
    is_interior: bool,
    within_face_class: Optional[str],
    externally_stable: Optional[bool],
) -> str:
    """Single categorical class used for downstream filtering."""
    if is_singular:
        return "singular"
    if not is_interior:
        return "non_interior"
    if within_face_class == "non_hyperbolic":
        return "non_hyperbolic"
    if within_face_class == "asymptotically_stable":
        return "asymp_stable" if externally_stable else "asymp_stable_invadable"
    if within_face_class == "unstable":
        return "unstable"
    if within_face_class == "saddle":
        return "saddle"
    raise RuntimeError(
        f"unreachable overall_class for (sing={is_singular}, "
        f"int={is_interior}, wfc={within_face_class}, ext={externally_stable})"
    )


def build_row(
    support_id: int,
    support: Sequence[int],
    names: Sequence[str],
    A: np.ndarray,
    tol: float,
) -> Dict[str, object]:
    """Solve, classify, and assemble one row of the result dataset."""
    n = A.shape[0]
    A_S = A[np.ix_(list(support), list(support))]
    sol: FaceSolution = solve_face(A_S, tol)

    row: Dict[str, object] = {
        "support_id": int(support_id),
        "support_tuple": support_tuple_str(support, names),
        "support_size": int(len(support)),
        "support_mask": support_bitmask(support, n),
    }
    # x_<TypeName> columns — NaN for types not in S or for singular rows
    for j, name in enumerate(names):
        row[f"x_{name}"] = float("nan")

    # Default values for downstream columns
    row["c"] = float("nan")
    row["c_crosscheck"] = float("nan")
    row["is_interior"] = False
    row["is_singular"] = bool(sol.is_singular)
    row["tangent_eigvals"] = "[]"
    row["max_re_eigval"] = float("nan")
    row["min_re_eigval"] = float("nan")
    row["has_complex_eigvals"] = False
    row["within_face_class"] = ""
    row["external_invasion_fitnesses"] = "{}"
    row["max_external_fitness"] = -math.inf
    row["externally_stable"] = True

    if sol.is_singular:
        row["overall_class"] = "singular"
        return row

    # Fill x and c
    assert sol.x is not None and sol.c is not None
    for local_idx, global_idx in enumerate(support):
        row[f"x_{names[global_idx]}"] = float(sol.x[local_idx])
    row["c"] = float(sol.c)
    row["c_crosscheck"] = float(sol.c_crosscheck) if sol.c_crosscheck is not None else float("nan")
    row["is_interior"] = bool(sol.is_interior)

    if not sol.is_interior:
        row["overall_class"] = "non_interior"
        return row

    # Within-face Jacobian eigenvalues
    J = replicator_jacobian(A_S, sol.x)
    eigs = tangent_eigvals(J)
    classified = classify_within_face(eigs, tol)
    row.update(classified)

    # External invasion fitness against types outside S
    f_ext = external_invasion_fitness(A, support, sol.x, sol.c)
    if f_ext.size == 0:
        max_ext = -math.inf
        row["external_invasion_fitnesses"] = "{}"
    else:
        in_support = set(support)
        outside_names = [names[k] for k in range(n) if k not in in_support]
        row["external_invasion_fitnesses"] = json.dumps(
            {nm: float(v) for nm, v in zip(outside_names, f_ext)}
        )
        max_ext = float(f_ext.max())
    row["max_external_fitness"] = max_ext
    row["externally_stable"] = bool(max_ext < -tol) if f_ext.size > 0 else True

    row["overall_class"] = classify_overall(
        is_singular=False,
        is_interior=True,
        within_face_class=classified["within_face_class"],
        externally_stable=row["externally_stable"],
    )
    return row

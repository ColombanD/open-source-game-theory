"""Stage (ii.c): face-equilibrium enumeration and classification.

For every non-empty support S ⊆ {1,…,N} with |S| ≥ 2, solve for the
unique interior fixed point x_S* of the replicator dynamics on Δ_S,
classify within-face stability via the tangent-space Jacobian, and
evaluate external invasion fitnesses for k ∉ S.

The canonical artefact is `results/faces/face_equilibria.parquet`.
"""

from .enumerate import enumerate_supports, support_bitmask, support_tuple_str
from .jacobian import (
    FaceSolution,
    solve_face,
    tangent_eigvals,
    external_invasion_fitness,
)
from .classify import (
    classify_within_face,
    classify_overall,
    build_row,
)
from .io import (
    OVERALL_CLASSES,
    columns_for,
    load_numeric_matrix,
    load_inherited_assumptions,
    write_parquet,
    write_csv,
    write_assumptions,
    write_summary_md,
)

__all__ = [
    "enumerate_supports",
    "support_bitmask",
    "support_tuple_str",
    "FaceSolution",
    "solve_face",
    "tangent_eigvals",
    "external_invasion_fitness",
    "classify_within_face",
    "classify_overall",
    "build_row",
    "columns_for",
    "OVERALL_CLASSES",
    "load_numeric_matrix",
    "load_inherited_assumptions",
    "write_parquet",
    "write_csv",
    "write_assumptions",
    "write_summary_md",
]

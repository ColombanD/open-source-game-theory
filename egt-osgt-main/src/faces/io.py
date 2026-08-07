"""I/O for the face-equilibrium stage.

Reads the numeric A from `results/ess/payoff_matrix_numeric.csv` (the
canonical artefact written by Stage (i)) and the inherited assumptions
from `results/ess/assumptions.json`. Writes parquet, CSV mirror,
`assumptions.json`, and `summary.md` under the chosen output directory.
"""

from __future__ import annotations

import csv
import importlib.metadata as md
import json
from pathlib import Path
from typing import Iterable, List, Optional, Tuple

import numpy as np  # type: ignore
import pandas as pd  # type: ignore


OVERALL_CLASSES = (
    "asymp_stable",
    "asymp_stable_invadable",
    "saddle",
    "unstable",
    "non_interior",
    "singular",
    "non_hyperbolic",
)


def columns_for(names: Iterable[str]) -> List[str]:
    """Frozen column ordering for the result dataset."""
    base_before = [
        "support_id",
        "support_tuple",
        "support_size",
        "support_mask",
    ]
    x_cols = [f"x_{n}" for n in names]
    base_after = [
        "c",
        "c_crosscheck",
        "is_interior",
        "is_singular",
        "tangent_eigvals",
        "max_re_eigval",
        "min_re_eigval",
        "has_complex_eigvals",
        "within_face_class",
        "external_invasion_fitnesses",
        "max_external_fitness",
        "externally_stable",
        "overall_class",
    ]
    return base_before + x_cols + base_after


def load_numeric_matrix(path: Path) -> Tuple[List[str], np.ndarray]:
    """Parse `payoff_matrix_numeric.csv` → (names, A).

    Same CSV shape used by `src/invasion/loader.py`: header row begins
    with an empty cell, then N type names; subsequent rows are labelled
    with the row type and contain N float entries.
    """
    path = Path(path)
    with open(path, newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        names = [h for h in header[1:] if h != ""]
        labels: List[str] = []
        rows: List[List[float]] = []
        for raw in reader:
            if not raw or all(c == "" for c in raw):
                continue
            label, *cells = raw
            labels.append(label)
            rows.append([float(c) for c in cells[: len(names)]])
    if labels != names:
        raise ValueError(
            f"Row labels {labels} do not match column header {names} in {path}"
        )
    A = np.array(rows, dtype=float)
    return names, A


def load_inherited_assumptions(path: Optional[Path]) -> Optional[dict]:
    """Read `results/ess/assumptions.json` if present."""
    if path is None:
        return None
    path = Path(path)
    if not path.exists():
        return None
    with open(path) as f:
        return json.load(f)


def _library_versions() -> dict:
    out = {}
    for lib in ("numpy", "scipy", "pandas", "pyarrow", "tqdm", "networkx"):
        try:
            out[lib] = md.version(lib)
        except Exception:
            pass
    return out


def write_parquet(df: pd.DataFrame, path: Path) -> None:
    """Write the result DataFrame to parquet (pyarrow engine)."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    df.to_parquet(path, index=False, engine="pyarrow")


def write_csv(df: pd.DataFrame, path: Path) -> None:
    """Write the CSV mirror. Booleans become 'True'/'False'; JSON
    strings (eigvals, external fitnesses) are written verbatim."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    df.to_csv(path, index=False)


def write_assumptions(
    out_path: Path,
    numeric_matrix_path: Path,
    inherited: Optional[dict],
    tol: float,
    n_supports: int,
    n_types: int,
) -> None:
    """Write `assumptions.json` describing the run."""
    out_path = Path(out_path)
    pd_payoffs = (inherited or {}).get("pd_payoffs", {})
    diagonal_policy = (inherited or {}).get("diagonal_undefined_policy") or {
        "note": "no inherited diagonal-undefined policy"
    }
    excluded = (inherited or {}).get("excluded_types") or {}
    undefined_cells = (inherited or {}).get("undefined_cells_resolved") or {}

    payload = {
        "stage": "face_equilibria",
        "faces_pipeline_version": "0.1.0",
        "numeric_matrix_source": str(numeric_matrix_path),
        "n_types": n_types,
        "n_supports_enumerated": n_supports,
        "tolerance": {
            "tol": tol,
            "rationale": (
                "single global tolerance used for: singular-system detection, "
                "is-interior threshold (x_i > tol), zero-real-part eigenvalue "
                "test for non-hyperbolicity, and external-stability test "
                "(max_external_fitness < -tol)."
            ),
        },
        "tangent_projection_method": (
            "orthonormal basis of {v in R^|S| : 1^T v = 0} from "
            "scipy.linalg.null_space; J_tan = Q^T J Q; eig via scipy.linalg.eig"
        ),
        "linear_solve_method": "scipy.linalg.solve on the (|S|+1)x(|S|+1) block system",
        "non_interior_policy": (
            "rows with is_interior=False have within-face Jacobian and "
            "eigenvalues NOT computed (tangent_eigvals='[]', max/min_re_eigval=NaN, "
            "has_complex_eigvals=False, within_face_class=''); external "
            "invasion fitnesses are not computed for non-interior solutions."
        ),
        "enumeration": (
            "every non-empty support S with |S| >= 2 is enumerated; no pruning "
            "by strict domination (Akin 1980) or any other criterion."
        ),
        "pd_payoffs": pd_payoffs,
        "excluded_types": excluded,
        "undefined_cells_resolved": undefined_cells,
        "diagonal_undefined_policy": diagonal_policy,
        "library_versions": _library_versions(),
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2)


def _counts_table(df: pd.DataFrame) -> str:
    counts = df["overall_class"].value_counts().to_dict()
    lines = ["| overall_class | count |", "| --- | --- |"]
    for cls in OVERALL_CLASSES:
        lines.append(f"| {cls} | {int(counts.get(cls, 0))} |")
    return "\n".join(lines)


def _format_cell(v) -> str:
    """Render a DataFrame cell for the summary markdown table.

    Floats are formatted with 6 significant figures; NaN and -inf are
    spelled out for readability; everything else is `str(v)`.
    """
    if isinstance(v, float):
        if v != v:  # NaN
            return "NaN"
        if v == float("-inf"):
            return "-inf"
        if v == float("inf"):
            return "inf"
        return f"{v:.6g}"
    return str(v)


def _row_listing(df: pd.DataFrame, mask: pd.Series, cols: List[str]) -> str:
    """Dependency-free markdown table (avoids pandas.to_markdown which
    requires the optional `tabulate` package)."""
    sub = df.loc[mask, cols]
    if sub.empty:
        return "_(none)_"
    header = "| " + " | ".join(cols) + " |"
    divider = "| " + " | ".join("---" for _ in cols) + " |"
    rows = [
        "| " + " | ".join(_format_cell(row[c]) for c in cols) + " |"
        for _, row in sub.iterrows()
    ]
    return "\n".join([header, divider] + rows)


def write_summary_md(
    df: pd.DataFrame,
    out_path: Path,
    names: List[str],
    numeric_matrix_path: Path,
) -> None:
    """Narrative summary that traces every claim to a row in the parquet."""
    out_path = Path(out_path)
    n = len(names)
    n_rows = len(df)

    stable_mask = df["overall_class"].isin(
        ["asymp_stable", "asymp_stable_invadable"]
    )
    singular_mask = df["overall_class"] == "singular"
    nh_mask = df["overall_class"] == "non_hyperbolic"

    listing_cols = [
        "support_id",
        "support_tuple",
        "support_size",
        "overall_class",
        "max_re_eigval",
        "max_external_fitness",
    ]

    body = [
        "# Face equilibria — summary",
        "",
        f"- Numeric matrix: `{numeric_matrix_path}`",
        f"- Number of types (N): **{n}**",
        f"- Supports enumerated (|S| >= 2): **{n_rows}**",
        "",
        "All claims below trace to specific rows in",
        "`face_equilibria.parquet` (column `support_id`).",
        "",
        "## Counts by overall_class",
        "",
        _counts_table(df),
        "",
        "## Asymptotically stable interior equilibria",
        "",
        "Rows with `overall_class` ∈ {`asymp_stable`, `asymp_stable_invadable`}.",
        "",
        _row_listing(df, stable_mask, listing_cols),
        "",
        "## Singular faces",
        "",
        "Rows with `A_SS` singular — equilibrium columns are NaN.",
        "",
        _row_listing(df, singular_mask, listing_cols),
        "",
        "## Non-hyperbolic faces",
        "",
        "Rows with at least one tangent eigenvalue on the imaginary axis "
        "(within numerical tolerance).",
        "",
        _row_listing(df, nh_mask, listing_cols),
        "",
    ]
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        f.write("\n".join(body))

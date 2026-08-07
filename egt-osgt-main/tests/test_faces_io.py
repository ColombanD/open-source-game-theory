"""Schema / round-trip checks for the face-equilibria dataset.

Build a small DataFrame via build_row over a tiny matrix; write to
parquet and CSV; reload and check column ordering, dtypes, and that
the |S|=2 single-eigenvalue JSON round-trips losslessly.
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pandas as pd

from src.faces.classify import build_row
from src.faces.enumerate import enumerate_supports
from src.faces.io import (
    OVERALL_CLASSES,
    columns_for,
    write_csv,
    write_parquet,
)


def _build_df_for_2x2(A, names, tol):
    rows = []
    for sid, support in enumerate(enumerate_supports(len(names))):
        rows.append(build_row(sid, support, names, A, tol))
    return pd.DataFrame(rows, columns=columns_for(names))


def test_schema_columns_for_hawk_dove(tmp_path: Path):
    V, C = 2.0, 4.0
    A = np.array([[(V - C) / 2.0, V], [0.0, V / 2.0]])
    names = ["H", "D"]
    df = _build_df_for_2x2(A, names, tol=1e-10)

    expected_cols = columns_for(names)
    assert list(df.columns) == expected_cols
    # 2 types => only 1 support of size >= 2 (the full one)
    assert len(df) == 1


def test_parquet_csv_round_trip_preserves_eigvals(tmp_path: Path):
    V, C = 2.0, 4.0
    A = np.array([[(V - C) / 2.0, V], [0.0, V / 2.0]])
    names = ["H", "D"]
    df = _build_df_for_2x2(A, names, tol=1e-10)

    parquet_path = tmp_path / "face_equilibria.parquet"
    csv_path = tmp_path / "face_equilibria.csv"
    write_parquet(df, parquet_path)
    write_csv(df, csv_path)

    df_pq = pd.read_parquet(parquet_path)
    df_csv = pd.read_csv(csv_path)

    assert list(df_pq.columns) == list(df.columns)
    assert list(df_csv.columns) == list(df.columns)

    # |S|=2 single eigenvalue JSON survives both formats
    eigs_pq = json.loads(df_pq.iloc[0]["tangent_eigvals"])
    eigs_csv = json.loads(df_csv.iloc[0]["tangent_eigvals"])
    assert len(eigs_pq) == 1
    assert len(eigs_csv) == 1
    assert abs(eigs_pq[0][0] - eigs_csv[0][0]) < 1e-12
    assert abs(eigs_pq[0][1] - eigs_csv[0][1]) < 1e-12

    # overall_class string survives
    assert df_pq.iloc[0]["overall_class"] == "asymp_stable"
    assert df_csv.iloc[0]["overall_class"] == "asymp_stable"


def test_overall_classes_constant_covers_what_classify_emits():
    # The OVERALL_CLASSES tuple should contain every class string the
    # classifier can emit. (Defensive check: keeps the summary table
    # consistent with the classifier.)
    expected = {
        "asymp_stable",
        "asymp_stable_invadable",
        "saddle",
        "unstable",
        "non_interior",
        "singular",
        "non_hyperbolic",
    }
    assert set(OVERALL_CLASSES) == expected

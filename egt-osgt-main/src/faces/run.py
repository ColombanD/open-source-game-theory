"""CLI entry point for the face-equilibrium stage.

Load numeric A → enumerate all supports |S| >= 2 → solve / classify
each → assemble a pandas DataFrame → write parquet + CSV mirror +
assumptions.json + summary.md under the chosen output directory.

Invocation (from repo root, via the project's conda env):

    conda run -n py-random python -m src.faces.run \
        --numeric-matrix        results/ess/payoff_matrix_numeric.csv \
        --inherited-assumptions results/ess/assumptions.json \
        --out-dir               results/faces/ \
        --tol                   1e-10
"""

from __future__ import annotations

import argparse
from pathlib import Path

import pandas as pd  # type: ignore
from tqdm import tqdm  # type: ignore

from .classify import build_row
from .enumerate import enumerate_supports
from .io import (
    columns_for,
    load_inherited_assumptions,
    load_numeric_matrix,
    write_assumptions,
    write_csv,
    write_parquet,
    write_summary_md,
)


def _count_supports(n: int) -> int:
    """Number of subsets of size >= 2 of an n-element set."""
    return (1 << n) - n - 1 if n >= 2 else 0


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--numeric-matrix",
        type=Path,
        default=Path("results/ess/payoff_matrix_numeric.csv"),
        help="path to results/ess/payoff_matrix_numeric.csv",
    )
    p.add_argument(
        "--inherited-assumptions",
        type=Path,
        default=Path("results/ess/assumptions.json"),
        help="path to results/ess/assumptions.json",
    )
    p.add_argument(
        "--out-dir",
        type=Path,
        default=Path("results/faces/"),
        help="output directory for parquet/CSV/assumptions/summary",
    )
    p.add_argument(
        "--tol",
        type=float,
        default=1e-10,
        help="global numerical tolerance (singular / zero-eigval / external-fit)",
    )
    args = p.parse_args()

    names, A = load_numeric_matrix(args.numeric_matrix)
    inherited = load_inherited_assumptions(args.inherited_assumptions)
    n = len(names)
    n_supports = _count_supports(n)

    print(
        f"Loaded N={n} types from {args.numeric_matrix}. "
        f"Enumerating {n_supports} supports."
    )

    rows = []
    for support_id, support in enumerate(
        tqdm(enumerate_supports(n), total=n_supports, unit="support")
    ):
        rows.append(build_row(support_id, support, names, A, args.tol))

    cols = columns_for(names)
    df = pd.DataFrame(rows, columns=cols)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    parquet_path = args.out_dir / "face_equilibria.parquet"
    csv_path = args.out_dir / "face_equilibria.csv"
    assumptions_path = args.out_dir / "assumptions.json"
    summary_path = args.out_dir / "summary.md"

    write_parquet(df, parquet_path)
    write_csv(df, csv_path)
    write_assumptions(
        out_path=assumptions_path,
        numeric_matrix_path=args.numeric_matrix,
        inherited=inherited,
        tol=args.tol,
        n_supports=len(df),
        n_types=n,
    )
    write_summary_md(
        df=df,
        out_path=summary_path,
        names=names,
        numeric_matrix_path=args.numeric_matrix,
    )

    print(f"Wrote {len(df)} rows to {parquet_path}.")


if __name__ == "__main__":
    main()

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
    p.add_argument(
        "--max-support-size",
        type=int,
        default=None,
        help=(
            "skip supports larger than this. Enumeration is 2^N - N - 1 "
            "(2036 at N=11, 32752 at N=15), each a linear solve plus an "
            "eigendecomposition, so a full sweep over many (t, α) points can "
            "want a bound. Any bound is RECORDED in assumptions.json — a "
            "truncated enumeration must never read as a complete one."
        ),
    )
    args = p.parse_args()

    run_faces(
        args.numeric_matrix,
        args.out_dir,
        inherited_assumptions=args.inherited_assumptions,
        tol=args.tol,
        max_support_size=args.max_support_size,
    )


def run_faces(
    numeric_matrix: Path,
    out_dir: Path,
    inherited_assumptions: Path | None = None,
    tol: float = 1e-10,
    max_support_size: int | None = None,
    progress: bool = True,
):
    """Enumerate and classify every face equilibrium; write the artefacts.

    Returns the assembled DataFrame. This is the library entry point the
    sweep driver and the API call.
    """
    names, A = load_numeric_matrix(numeric_matrix)
    inherited = load_inherited_assumptions(inherited_assumptions)
    n = len(names)
    n_supports = _count_supports(n)

    if progress:
        print(
            f"Loaded N={n} types from {numeric_matrix}. "
            f"Enumerating {n_supports} supports."
        )

    supports = enumerate_supports(n)
    if max_support_size is not None:
        supports = (s for s in supports if len(s) <= max_support_size)

    rows = []
    iterator = (
        tqdm(supports, total=n_supports, unit="support") if progress else supports
    )
    for support_id, support in enumerate(iterator):
        rows.append(build_row(support_id, support, names, A, tol))

    df = pd.DataFrame(rows, columns=columns_for(names))

    out_dir.mkdir(parents=True, exist_ok=True)
    parquet_path = out_dir / "face_equilibria.parquet"

    write_parquet(df, parquet_path)
    write_csv(df, out_dir / "face_equilibria.csv")
    write_assumptions(
        out_path=out_dir / "assumptions.json",
        numeric_matrix_path=numeric_matrix,
        inherited=inherited,
        tol=tol,
        n_supports=len(df),
        n_types=n,
        max_support_size=max_support_size,
    )
    write_summary_md(
        df=df,
        out_path=out_dir / "summary.md",
        names=names,
        numeric_matrix_path=numeric_matrix,
        max_support_size=max_support_size,
    )

    if progress:
        print(f"Wrote {len(df)} rows to {parquet_path}.")
    return df


if __name__ == "__main__":
    main()

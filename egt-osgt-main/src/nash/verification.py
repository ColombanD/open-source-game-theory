"""Exact-arithmetic best-response verification on the original (unshifted) A.

For the bimatrix game (A, B) with B = A^T (B[i,j] = A[j,i] = col's payoff
when row plays i, col plays j) and a candidate NE (xi, eta):

  row payoff  u = sum_{i,j} xi[i] A[i,j] eta[j] = xi^T A eta
  col payoff  v = sum_{i,j} xi[i] eta[j] B[i,j] = sum_{i,j} xi[i] eta[j] A[j,i]
              = sum_j eta[j] (A xi)[j] = eta^T A xi

Conditions:
  - Row's BR vector is (A eta) with (A eta)[i] = sum_j A[i,j] eta[j];
    for all i: (A eta)[i] ≤ u, with equality on support(xi).
  - Col's BR vector is (A xi) read along rows, i.e. (Axi_col)[j]
    = sum_i A[j,i] xi[i] (note: this is NOT A^T xi unless A is symmetric);
    for all j: (Axi_col)[j] ≤ v, with equality on support(eta).

All comparisons are exact Fraction operations.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import List, Tuple

from src.nash.reconcile import ReconciledNE


@dataclass(frozen=True)
class VerificationFailure:
    ne_index: int
    side: str                # "row" or "col"
    strategy: int            # which i (or j) failed
    rel: str                 # "BR_strict_violation" or "support_payoff_mismatch"
    expected: Fraction       # u or v
    got: Fraction            # (A eta)_i or (A^T xi)_j


@dataclass(frozen=True)
class VerifiedNE:
    ne_index: int
    u: Fraction
    v: Fraction


def _mat_vec(A: List[List[Fraction]], v: Tuple[Fraction, ...]) -> List[Fraction]:
    n = len(A)
    return [sum(A[i][j] * v[j] for j in range(n)) for i in range(n)]


def _vec_dot(u: Tuple[Fraction, ...], v: List[Fraction]) -> Fraction:
    return sum(u[i] * v[i] for i in range(len(u)))


def verify_all(
    A: List[List[Fraction]],
    merged: List[ReconciledNE],
) -> Tuple[List[VerifiedNE], List[VerificationFailure]]:
    """Verify every reconciled NE on the original A. Returns (passed, failures)."""
    passed: List[VerifiedNE] = []
    failures: List[VerificationFailure] = []
    n = len(A)

    for idx, ne in enumerate(merged):
        if len(ne.xi) != n or len(ne.eta) != n:
            failures.append(
                VerificationFailure(
                    ne_index=idx, side="row", strategy=-1,
                    rel="dimension_mismatch",
                    expected=Fraction(n), got=Fraction(len(ne.xi)),
                )
            )
            continue
        # Row's BR vector: (A eta)[i] = sum_j A[i,j] eta[j].
        A_eta = _mat_vec(A, ne.eta)
        u = _vec_dot(ne.xi, A_eta)
        # Col's BR vector: (A_xi_col)[j] = sum_i A[j,i] xi[i], because
        # B = A^T means col's payoff when (row=i, col=j) is A[j,i].
        Axi_col = [sum(A[j][i] * ne.xi[i] for i in range(n)) for j in range(n)]
        v = _vec_dot(ne.eta, Axi_col)

        ok = True
        for i in range(n):
            if A_eta[i] > u:
                failures.append(
                    VerificationFailure(
                        ne_index=idx, side="row", strategy=i,
                        rel="BR_strict_violation",
                        expected=u, got=A_eta[i],
                    )
                )
                ok = False
            if ne.xi[i] > 0 and A_eta[i] != u:
                failures.append(
                    VerificationFailure(
                        ne_index=idx, side="row", strategy=i,
                        rel="support_payoff_mismatch",
                        expected=u, got=A_eta[i],
                    )
                )
                ok = False
        for j in range(n):
            if Axi_col[j] > v:
                failures.append(
                    VerificationFailure(
                        ne_index=idx, side="col", strategy=j,
                        rel="BR_strict_violation",
                        expected=v, got=Axi_col[j],
                    )
                )
                ok = False
            if ne.eta[j] > 0 and Axi_col[j] != v:
                failures.append(
                    VerificationFailure(
                        ne_index=idx, side="col", strategy=j,
                        rel="support_payoff_mismatch",
                        expected=v, got=Axi_col[j],
                    )
                )
                ok = False
        if ok:
            passed.append(VerifiedNE(ne_index=idx, u=u, v=v))

    return passed, failures

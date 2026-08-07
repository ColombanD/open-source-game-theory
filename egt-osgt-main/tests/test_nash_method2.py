"""Synthetic-game tests for Method 2 (pygambit + lrsnash)."""

from __future__ import annotations

from fractions import Fraction
from typing import List, Set, Tuple

import numpy as np
import pytest

from src.nash.classification import classify_all
from src.nash.game_construction import build_bimatrix
from src.nash.method2_lrsnash import enumerate_lrsnash
from src.nash.method2_pygambit import enumerate_pygambit
from src.nash.payoff_shift import shift_to_positive
from src.nash.pure_ne import enumerate_pure
from src.nash.reconcile import reconcile
from src.nash.verification import verify_all


F = Fraction


def _enumerate_both(A_np: np.ndarray):
    A_frac, _ = build_bimatrix(A_np)
    A_shifted, shift = shift_to_positive(A_frac)
    n = len(A_shifted)
    B_shifted = [[A_shifted[j][i] for j in range(n)] for i in range(n)]
    pg = enumerate_pygambit(A_shifted, B_shifted)
    lr = enumerate_lrsnash(A_shifted, B_shifted)
    merged, agree, diff = reconcile(pg, lr)
    return A_frac, merged, agree, diff


def _ne_keys(merged) -> Set[Tuple[Tuple[F, ...], Tuple[F, ...]]]:
    return {(ne.xi, ne.eta) for ne in merged}


def test_hawk_dove_finds_three_extreme_NE():
    # A = [[0, 3], [1, 2]] over strategies (H, D).
    # Pure asymmetric NE: (H, D) and (D, H); mixed symmetric (1/2, 1/2).
    A = np.array([[0, 3], [1, 2]], dtype=float)
    A_frac, merged, agree, diff = _enumerate_both(A)
    assert agree, f"libraries disagree: {diff}"
    keys = _ne_keys(merged)
    expected = {
        ((F(0), F(1)), (F(1), F(0))),       # (D, H)
        ((F(1), F(0)), (F(0), F(1))),       # (H, D)
        ((F(1, 2), F(1, 2)), (F(1, 2), F(1, 2))),  # mixed symmetric
    }
    assert keys == expected

    verified, failures = verify_all(A_frac, merged)
    assert not failures
    # Symmetric mixed payoff: u = v = 3/2.
    sym = next(v for v in verified
               if merged[v.ne_index].xi == (F(1, 2), F(1, 2)))
    assert sym.u == F(3, 2) and sym.v == F(3, 2)


def test_coordination_2x2_finds_three_NE():
    # A = [[2, 0], [0, 1]] symmetric. Two pure symmetric + one mixed (1/3, 2/3).
    A = np.array([[2, 0], [0, 1]], dtype=float)
    A_frac, merged, agree, diff = _enumerate_both(A)
    assert agree
    keys = _ne_keys(merged)
    expected = {
        ((F(1), F(0)), (F(1), F(0))),
        ((F(0), F(1)), (F(0), F(1))),
        ((F(1, 3), F(2, 3)), (F(1, 3), F(2, 3))),
    }
    assert keys == expected

    verified, failures = verify_all(A_frac, merged)
    assert not failures
    mixed = next(v for v in verified
                 if merged[v.ne_index].xi == (F(1, 3), F(2, 3)))
    assert mixed.u == F(2, 3) and mixed.v == F(2, 3)


def test_rock_paper_scissors_finds_uniform_symmetric_NE():
    # Zero-sum, no pure NE; unique symmetric NE (1/3, 1/3, 1/3) with u = v = 0.
    A = np.array([[0, -1, 1], [1, 0, -1], [-1, 1, 0]], dtype=float)
    A_frac, merged, agree, diff = _enumerate_both(A)
    assert agree
    third = (F(1, 3), F(1, 3), F(1, 3))
    assert (third, third) in _ne_keys(merged)

    verified, failures = verify_all(A_frac, merged)
    assert not failures
    sym = next(v for v in verified if merged[v.ne_index].xi == third)
    assert sym.u == 0 and sym.v == 0


def test_pure_ne_enumerator_matches_method2_on_small_games():
    A = np.array([[2, 0], [0, 1]], dtype=float)
    pure_keys = {(p.i, p.j) for p in enumerate_pure(A)}
    _, merged, agree, _ = _enumerate_both(A)
    assert agree
    method2_pure = {
        (ne.support_x[0], ne.support_y[0])
        for ne in merged
        if len(ne.support_x) == 1 and len(ne.support_y) == 1
    }
    assert pure_keys <= method2_pure


def test_classify_symmetric_vs_asymmetric_pairs_hawk_dove():
    A = np.array([[0, 3], [1, 2]], dtype=float)
    A_frac, merged, _, _ = _enumerate_both(A)
    classified = classify_all(A_frac, merged)
    sym = [c for c in classified if c.classification == "symmetric"]
    asym = [c for c in classified if c.classification == "asymmetric"]
    assert len(sym) == 1
    assert len(asym) == 2
    pair_ids = {c.asymmetric_pair_id for c in asym}
    # Both asymmetric NE share a pair_id.
    assert len(pair_ids) == 1 and None not in pair_ids

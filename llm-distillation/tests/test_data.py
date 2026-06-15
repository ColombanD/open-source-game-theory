"""Parsing tests: cell encoding, C/D -> 1/0, no transpose, input vectors."""

from __future__ import annotations

import numpy as np
import pytest

from distillation.data import (
    load_input_vector,
    load_library,
    parse_cd_string,
    parse_cell,
)

# A tiny synthetic matrix whose row actions differ from column actions, so a
# transpose bug would be caught. Row i's own actions are the FIRST element.
#   A vs A=(C,C)  A vs B=(C,D)   -> r_A = [C, C] = [1, 1]
#   B vs A=(D,C)  B vs B=(D,D)   -> r_B = [D, D] = [0, 0]
TINY_CSV = """,A,B
A,"(C, C)","(C, D)"
B,"(D, C)","(D, D)"
"""


def write_csv(tmp_path, text):
    path = tmp_path / "m.csv"
    path.write_text(text)
    return path


def test_parse_cell_formats():
    assert parse_cell("(C, D)") == (1.0, 0.0)
    assert parse_cell("(D,C)") == (0.0, 1.0)
    assert parse_cell("C,D") == (1.0, 0.0)
    assert parse_cell("CD") == (1.0, 0.0)
    assert parse_cell("  (D, D) ") == (0.0, 0.0)


def test_parse_cell_rejects_garbage():
    with pytest.raises(ValueError):
        parse_cell("(X, C)")


def test_reference_matrix_uses_row_action_no_transpose(tmp_path):
    lib = load_library(write_csv(tmp_path, TINY_CSV))
    assert lib.bots == ("A", "B")
    # r_A is row A's OWN actions = first element of each pair = [1, 1].
    # r_B = [0, 0]. A transpose bug would give column actions [1, 0] / [0, 0].
    expected = np.array([[1.0, 1.0], [0.0, 0.0]])
    np.testing.assert_array_equal(lib.R, expected)


def test_cd_maps_to_one_zero():
    np.testing.assert_array_equal(parse_cd_string("CDDC"), [1.0, 0.0, 0.0, 1.0])


def test_non_square_rejected(tmp_path):
    bad = ',A,B\nA,"(C, C)"\n'
    with pytest.raises(ValueError):
        load_library(write_csv(tmp_path, bad))


def test_row_column_mismatch_rejected(tmp_path):
    bad = ',A,B\nA,"(C, C)","(C, D)"\nC,"(D, C)","(D, D)"\n'
    with pytest.raises(ValueError):
        load_library(write_csv(tmp_path, bad))


def test_load_input_vector_cd_string():
    x = load_input_vector("CDCD", 4)
    np.testing.assert_array_equal(x, [1.0, 0.0, 1.0, 0.0])


def test_load_input_vector_json_file(tmp_path):
    p = tmp_path / "x.json"
    p.write_text("[1.0, 0.0, 0.5, 0.25]")
    np.testing.assert_array_equal(load_input_vector(p, 4), [1.0, 0.0, 0.5, 0.25])


def test_load_input_vector_csv_floats(tmp_path):
    p = tmp_path / "x.csv"
    p.write_text("1, 0, 0.5, 0.25")
    np.testing.assert_array_equal(load_input_vector(p, 4), [1.0, 0.0, 0.5, 0.25])


def test_load_input_vector_length_mismatch():
    with pytest.raises(ValueError):
        load_input_vector("CDC", 4)


def test_load_input_vector_out_of_range():
    with pytest.raises(ValueError):
        load_input_vector("1.5, 0, 0, 0", 4)


def test_real_matrix_has_identical_rows():
    """The shipped matrix really does contain coincident rows (Cupod==Dupoc)."""
    from pathlib import Path

    root = Path(__file__).resolve().parents[1]
    lib = load_library(root / "data" / "payoff_matrix.csv")
    i = lib.bots.index("CupodBot")
    j = lib.bots.index("DupocBot")
    np.testing.assert_array_equal(lib.R[i], lib.R[j])

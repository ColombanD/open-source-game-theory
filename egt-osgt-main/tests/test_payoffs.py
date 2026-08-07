"""Tests for the PD parameter validator: requires b > c > 0 (strict)."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from src.ingest.payoffs import validate_pd_params  # noqa: E402


def test_default_params_are_valid():
    """The defaults shipped in config.json (b=3, c=1) must be a valid PD."""
    validate_pd_params(b=3.0, c=1.0)


@pytest.mark.parametrize("b,c", [(2.0, 1.0), (3.0, 1.0), (1.5, 0.5), (10.0, 9.999)])
def test_valid_pd_params_do_not_raise(b, c):
    validate_pd_params(b=b, c=c)


@pytest.mark.parametrize("c", [0.0, -0.1, -1.0])
def test_c_must_be_strictly_positive(c):
    with pytest.raises(ValueError, match="c must be > 0"):
        validate_pd_params(b=3.0, c=c)


@pytest.mark.parametrize("b,c", [(1.0, 1.0), (0.5, 1.0), (1.0, 2.0), (-1.0, 1.0)])
def test_b_must_strictly_exceed_c(b, c):
    with pytest.raises(ValueError, match="b must be > c"):
        validate_pd_params(b=b, c=c)


def test_non_numeric_inputs_raise():
    with pytest.raises(TypeError):
        validate_pd_params(b="3", c=1.0)  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        validate_pd_params(b=3.0, c=None)  # type: ignore[arg-type]

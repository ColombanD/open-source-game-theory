import pytest

from pd_runner.lean.templates import parse_bot_expr, select_action_claim_theorem


def test_select_action_claim_theorem_known_mapping() -> None:
    result = select_action_claim_theorem("dBot", "defectBot", "C", "D")
    assert result == ("DBot_vs_DefectBot", False)


def test_select_action_claim_theorem_unknown_mapping() -> None:
    with pytest.raises(ValueError, match="unknown bot: alternator"):
        select_action_claim_theorem("alternator", "cooperateBot", "C", "D")


def test_select_action_claim_theorem_reversed_mapping() -> None:
    """Test that reversed theorems are found and marked as reversed."""
    # OBot vs DBot has a theorem (D, C).
    # Request DBot vs OBot with (C, D) should find the reversed theorem.
    result = select_action_claim_theorem("dBot", "oBot", "C", "D")
    assert result == ("OBot_vs_DBot", True)


def test_parse_bot_expr_parameter_alias() -> None:
    expr = parse_bot_expr("cupodbot:3")

    assert expr.name == "CupodBot"
    assert expr.arg == "3"


def test_select_action_claim_theorem_parameterized_mapping() -> None:
    result = select_action_claim_theorem("CupodBot:3", "CooperateBot", "C", "C")
    assert result == ("CupodBot_vs_CooperateBot", False)

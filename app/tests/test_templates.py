from pd_runner.lean.templates import select_action_claim_theorem


def test_select_action_claim_theorem_known_mapping() -> None:
    result = select_action_claim_theorem("dBot", "defectBot", "C", "D")
    assert result == ("DBot_vs_DefectBot", False)


def test_select_action_claim_theorem_unknown_mapping() -> None:
    result = select_action_claim_theorem("alternator", "cooperateBot", "C", "D")
    assert result is None


def test_select_action_claim_theorem_reversed_mapping() -> None:
    """Test that reversed theorems are found and marked as reversed."""
    # OBot vs DBot has a theorem (D, C).
    # Request DBot vs OBot with (C, D) should find the reversed theorem.
    result = select_action_claim_theorem("dBot", "oBot", "C", "D")
    assert result == ("OBot_vs_DBot", True)

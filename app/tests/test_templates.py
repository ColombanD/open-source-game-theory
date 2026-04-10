from pd_runner.lean.templates import select_action_claim_theorem


def test_select_action_claim_theorem_known_mapping() -> None:
    result = select_action_claim_theorem("dBot", "defectBot", "C", "D")
    assert result == ("dbot_vs_defect_actionClaim", False)


def test_select_action_claim_theorem_unknown_mapping() -> None:
    result = select_action_claim_theorem("alternator", "cooperateBot", "C", "D")
    assert result is None


def test_select_action_claim_theorem_reversed_mapping() -> None:
    """Test that reversed theorems are found and marked as reversed."""
    # oBot vs dBot has a theorem (D, C)
    # Request dBot vs oBot with (C, D) should find the reversed theorem
    result = select_action_claim_theorem("dBot", "oBot", "C", "D")
    assert result == ("oBot_vs_dBot_actionClaim", True)
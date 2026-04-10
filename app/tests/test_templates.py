from pd_runner.lean.templates import select_action_claim_theorem


def test_select_action_claim_theorem_known_mapping() -> None:
    theorem = select_action_claim_theorem("dBot", "defectBot", "C", "D")
    assert theorem == "dbot_vs_defect_actionClaim"


def test_select_action_claim_theorem_unknown_mapping() -> None:
    theorem = select_action_claim_theorem("alternator", "cooperateBot", "C", "D")
    assert theorem is None
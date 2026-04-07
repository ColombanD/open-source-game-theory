from pd_runner.lean.templates import select_action_claim_theorem


def test_select_action_claim_theorem_known_mapping() -> None:
    theorem = select_action_claim_theorem("cooperateBot", "defectBot", "C", "D")
    assert theorem == "cd_actionClaim"


def test_select_action_claim_theorem_unknown_mapping() -> None:
    theorem = select_action_claim_theorem("alternator", "cooperateBot", "C", "D")
    assert theorem is None
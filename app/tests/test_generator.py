from pathlib import Path

from pd_runner.lean.generator import write_matchup_lean_file


def test_write_matchup_lean_file(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "dBot", "defectBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.path.exists()
    assert "import PrisonersDilemma.Models.BotUniverse" in content
    assert generated.proof_theorem_used == "PD.Proofs.DBot.dbot_vs_defect_actionClaim"
    assert "exact PD.Proofs.DBot.dbot_vs_defect_actionClaim" in content
    assert "#eval playActions Bot.dBot Bot.defectBot" in content


def test_write_matchup_lean_file_uses_preproved_theorem(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(
        tmp_path,
        "dBot",
        "defectBot",
        claim_left_action="C",
        claim_right_action="D",
    )
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PD.Proofs.DBot.dbot_vs_defect_actionClaim"
    assert "exact PD.Proofs.DBot.dbot_vs_defect_actionClaim" in content


def test_write_matchup_lean_file_falls_back_to_generated_proof(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(
        tmp_path,
        "alternator",
        "cooperateBot",
        claim_left_action="C",
        claim_right_action="D",
    )
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "generated:unfold+simp"
    assert "unfold ActionClaim playActions" in content


def test_write_matchup_lean_file_without_known_theorem_has_no_proof_block(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "alternator", "cooperateBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used is None
    assert "theorem claimed_actions" not in content

from pathlib import Path

from pd_runner.lean.generator import write_matchup_lean_file


def test_write_matchup_lean_file(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "dBot", "defectBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.path.exists()
    assert "import PrisonersDilemma" in content
    assert generated.proof_theorem_used == "PDNew.Theorems.DBot_vs_DefectBot"
    assert "exact PDNew.Theorems.DBot_vs_DefectBot 0" in content
    assert "#eval ((Action.C, Action.D) : Outcome)" in content


def test_write_matchup_lean_file_uses_preproved_theorem(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(
        tmp_path,
        "dBot",
        "defectBot",
        claim_left_action="C",
        claim_right_action="D",
    )
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.DBot_vs_DefectBot"
    assert "exact PDNew.Theorems.DBot_vs_DefectBot 0" in content


def test_write_matchup_lean_file_falls_back_to_generated_proof(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(
        tmp_path,
        "cooperateBot",
        "defectBot",
        claim_left_action="C",
        claim_right_action="D",
    )
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.outcome_CooperateBot_vs_DefectBot"
    assert "theorem claimed_outcome" in content


def test_write_matchup_lean_file_without_known_theorem_has_no_proof_block(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "alternator", "cooperateBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used is None
    assert "theorem claimed_actions" not in content
    assert "#check outcome 20 alternator CooperateBot" in content

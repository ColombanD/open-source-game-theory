from pathlib import Path

import pytest

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
    with pytest.raises(ValueError, match="unknown bot: alternator"):
        write_matchup_lean_file(tmp_path, "alternator", "cooperateBot")


def test_write_matchup_lean_file_uses_parameterized_universal_theorem(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "CupodBot:3", "CooperateBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.CupodBot_vs_CooperateBot"
    assert generated.result_kind == "concrete"
    assert "outcome (0 + 2) (CupodBot 3) CooperateBot" in content
    assert "exact PDNew.Theorems.CupodBot_vs_CooperateBot 3 0" in content
    assert "#eval ((Action.C, Action.C) : Outcome)" in content


def test_write_matchup_lean_file_uses_reversed_parameterized_universal_theorem(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "CooperateBot", "CupodBot:3")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.CupodBot_vs_CooperateBot"
    assert generated.actions_are_swapped is True
    assert "outcome (0 + 2) (CupodBot 3) CooperateBot" in content


def test_write_matchup_lean_file_uses_existential_theorem(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "CupodBot:?", "DefectBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.CupodBot_vs_DefectBot"
    assert generated.result_kind == "exists_parameter"
    assert "theorem claimed_exists_outcome" in content
    assert "∃ k, outcome (0 + 2) (CupodBot k) DefectBot" in content
    assert "exact PDNew.Theorems.CupodBot_vs_DefectBot 0" in content


def test_write_matchup_lean_file_prefers_universal_theorem_for_wildcard(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "CooperateBot", "CupodBot:?")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used == "PDNew.Theorems.CupodBot_vs_CooperateBot"
    assert generated.result_kind == "all_parameters"
    assert generated.witness == "any"
    assert generated.actions_are_swapped is True
    assert "exact PDNew.Theorems.CupodBot_vs_CooperateBot 0 0" in content


def test_write_matchup_lean_file_does_not_use_existential_for_concrete_param(tmp_path: Path) -> None:
    generated = write_matchup_lean_file(tmp_path, "CupodBot:3", "DefectBot")
    content = generated.path.read_text(encoding="utf-8")

    assert generated.proof_theorem_used is None
    assert "claimed_exists_outcome" not in content
    assert "#check outcome 20 (CupodBot 3) DefectBot" in content

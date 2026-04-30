from pathlib import Path
from types import SimpleNamespace

import pytest

from pd_runner.lean.executor import LeanExecResult
from pd_runner.lean.generator import GeneratedLeanFile
from pd_runner.models import MatchupRequest
from pd_runner.services import matchup_service


def test_run_matchup_orchestrates_generation_execution_and_parsing(monkeypatch, tmp_path: Path) -> None:
    generated_file = tmp_path / "matchup.lean"
    calls = {}

    monkeypatch.setattr(
        matchup_service,
        "load_paths",
        lambda: SimpleNamespace(
            generated_lean_dir=tmp_path / "generated",
            lean_engine_dir=tmp_path / "engine",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "write_matchup_lean_file",
        lambda **kwargs: GeneratedLeanFile(
            path=generated_file,
            proof_theorem_used="PD.Proofs.OpenSourceBots.cd_actionClaim",
            actions_are_swapped=False,
        ),
    )

    def fake_run_lean_file(lean_project_dir, lean_file):
        calls["run_after_build"] = calls.get("build_lean_project") is True
        calls["lean_project_dir"] = lean_project_dir
        calls["lean_file"] = lean_file
        return LeanExecResult(
            command=f"lake env lean {lean_file}",
            returncode=0,
            stdout="(C, D)\n",
            stderr="",
        )

    def fake_build_lean_project(lean_project_dir):
        calls["build_lean_project"] = True
        calls["build_project_dir"] = lean_project_dir
        return LeanExecResult(
            command="lake build PrisonersDilemma",
            returncode=0,
            stdout="",
            stderr="",
        )

    monkeypatch.setattr(matchup_service, "build_lean_project", fake_build_lean_project)
    def fake_parse_actions_from_stdout(stdout: str):
        calls["stdout"] = stdout
        return "C", "D"

    monkeypatch.setattr(matchup_service, "run_lean_file", fake_run_lean_file)
    monkeypatch.setattr(matchup_service, "parse_actions_from_stdout", fake_parse_actions_from_stdout)

    result = matchup_service.run_matchup(MatchupRequest("cooperateBot", "defectBot"))

    assert calls["build_project_dir"] == tmp_path / "engine"
    assert calls["run_after_build"] is True
    assert calls["lean_project_dir"] == tmp_path / "engine"
    assert calls["lean_file"] == generated_file
    assert calls["stdout"] == "(C, D)\n"
    assert result.left_bot == "cooperateBot"
    assert result.right_bot == "defectBot"
    assert result.left_action == "C"
    assert result.right_action == "D"
    assert result.lean_file == str(generated_file)
    assert result.command == f"lake env lean {generated_file}"
    assert result.proof_theorem_used == "PD.Proofs.OpenSourceBots.cd_actionClaim"


def test_run_matchup_swaps_actions_when_reversed_theorem_used(monkeypatch, tmp_path: Path) -> None:
    """When a reversed-order theorem is used, actions should be swapped to match requested order."""
    generated_file = tmp_path / "matchup.lean"

    monkeypatch.setattr(
        matchup_service,
        "load_paths",
        lambda: SimpleNamespace(
            generated_lean_dir=tmp_path / "generated",
            lean_engine_dir=tmp_path / "engine",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "write_matchup_lean_file",
        lambda **kwargs: GeneratedLeanFile(
            path=generated_file,
            proof_theorem_used="PD.Proofs.OpenSourceBots.dBot_vs_oBot_actionClaim",
            actions_are_swapped=True,  # Indicate that reversed theorem was used
        ),
    )

    def fake_run_lean_file(lean_project_dir, lean_file):
        # When we evaluate in reverse order, Lean returns the actions for that order
        return LeanExecResult(
            command=f"lake env lean {lean_file}",
            returncode=0,
            stdout="(D, C)\n",  # Actions for (dBot, oBot)
            stderr="",
        )

    monkeypatch.setattr(
        matchup_service,
        "build_lean_project",
        lambda lean_project_dir: LeanExecResult(
            command="lake build PrisonersDilemma",
            returncode=0,
            stdout="",
            stderr="",
        ),
    )
    def fake_parse_actions_from_stdout(stdout: str):
        return "D", "C"

    monkeypatch.setattr(matchup_service, "run_lean_file", fake_run_lean_file)
    monkeypatch.setattr(matchup_service, "parse_actions_from_stdout", fake_parse_actions_from_stdout)

    # Request oBot vs dBot (which doesn't have a direct theorem)
    result = matchup_service.run_matchup(MatchupRequest("oBot", "dBot"))

    # The actions should be swapped to match the requested order
    assert result.left_bot == "oBot"
    assert result.right_bot == "dBot"
    assert result.left_action == "C"  # Swapped from the reversed evaluation
    assert result.right_action == "D"  # Swapped from the reversed evaluation


def test_run_matchup_raises_and_cleans_up_on_lean_failure(monkeypatch, tmp_path: Path) -> None:
    generated_file = tmp_path / "matchup.lean"
    generated_file.write_text("fake lean file", encoding="utf-8")

    monkeypatch.setattr(
        matchup_service,
        "load_paths",
        lambda: SimpleNamespace(
            generated_lean_dir=tmp_path / "generated",
            lean_engine_dir=tmp_path / "engine",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "write_matchup_lean_file",
        lambda **kwargs: GeneratedLeanFile(
            path=generated_file,
            proof_theorem_used="PDNew.Theorems.outcome_CooperateBot_vs_DefectBot",
            actions_are_swapped=False,
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "run_lean_file",
        lambda lean_project_dir, lean_file: LeanExecResult(
            command=f"lake env lean {lean_file}",
            returncode=1,
            stdout="",
            stderr="boom",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "build_lean_project",
        lambda lean_project_dir: LeanExecResult(
            command="lake build PrisonersDilemma",
            returncode=0,
            stdout="",
            stderr="",
        ),
    )

    with pytest.raises(RuntimeError, match="lean execution failed"):
        matchup_service.run_matchup(MatchupRequest("cooperateBot", "defectBot"), keep_file=False)

    assert not generated_file.exists()


def test_run_matchup_raises_and_cleans_up_on_build_failure(monkeypatch, tmp_path: Path) -> None:
    generated_file = tmp_path / "matchup.lean"
    generated_file.write_text("fake lean file", encoding="utf-8")

    monkeypatch.setattr(
        matchup_service,
        "load_paths",
        lambda: SimpleNamespace(
            generated_lean_dir=tmp_path / "generated",
            lean_engine_dir=tmp_path / "engine",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "write_matchup_lean_file",
        lambda **kwargs: GeneratedLeanFile(
            path=generated_file,
            proof_theorem_used="PDNew.Theorems.outcome_CooperateBot_vs_DefectBot",
            actions_are_swapped=False,
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "build_lean_project",
        lambda lean_project_dir: LeanExecResult(
            command="lake build PrisonersDilemma",
            returncode=1,
            stdout="build stdout",
            stderr="build boom",
        ),
    )

    with pytest.raises(RuntimeError, match="lean engine build failed"):
        matchup_service.run_matchup(MatchupRequest("cooperateBot", "defectBot"), keep_file=False)

    assert not generated_file.exists()


def test_run_matchup_raises_when_no_outcome_theorem(monkeypatch, tmp_path: Path) -> None:
    generated_file = tmp_path / "matchup.lean"
    generated_file.write_text("fake lean file", encoding="utf-8")

    monkeypatch.setattr(
        matchup_service,
        "load_paths",
        lambda: SimpleNamespace(
            generated_lean_dir=tmp_path / "generated",
            lean_engine_dir=tmp_path / "engine",
        ),
    )
    monkeypatch.setattr(
        matchup_service,
        "write_matchup_lean_file",
        lambda **kwargs: GeneratedLeanFile(
            path=generated_file,
            proof_theorem_used=None,
            actions_are_swapped=False,
        ),
    )

    with pytest.raises(RuntimeError, match="no Lean outcome theorem"):
        matchup_service.run_matchup(MatchupRequest("unknown", "defectBot"), keep_file=False)

    assert not generated_file.exists()

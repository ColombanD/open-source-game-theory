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
        lambda **kwargs: GeneratedLeanFile(path=generated_file, proof_theorem_used="PD.Proofs.OpenSourceBots.cd_actionClaim"),
    )

    def fake_run_lean_file(lean_project_dir, lean_file):
        calls["lean_project_dir"] = lean_project_dir
        calls["lean_file"] = lean_file
        return LeanExecResult(
            command=f"lake env lean {lean_file}",
            returncode=0,
            stdout="(C, D)\n",
            stderr="",
        )

    def fake_parse_actions_from_stdout(stdout: str):
        calls["stdout"] = stdout
        return "C", "D"

    monkeypatch.setattr(matchup_service, "run_lean_file", fake_run_lean_file)
    monkeypatch.setattr(matchup_service, "parse_actions_from_stdout", fake_parse_actions_from_stdout)

    result = matchup_service.run_matchup(MatchupRequest("cooperateBot", "defectBot"))

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
        lambda **kwargs: GeneratedLeanFile(path=generated_file, proof_theorem_used=None),
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

    with pytest.raises(RuntimeError, match="lean execution failed"):
        matchup_service.run_matchup(MatchupRequest("cooperateBot", "defectBot"), keep_file=False)

    assert not generated_file.exists()
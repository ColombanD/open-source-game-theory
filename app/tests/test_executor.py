from pathlib import Path
from types import SimpleNamespace

from pd_runner.lean import executor as lean_executor


def test_run_lean_file_invokes_lake_env_lean(monkeypatch, tmp_path: Path) -> None:
    seen = {}

    def fake_run(cmd, cwd, capture_output, text, check):
        seen["cmd"] = cmd
        seen["cwd"] = cwd
        seen["capture_output"] = capture_output
        seen["text"] = text
        seen["check"] = check
        return SimpleNamespace(returncode=0, stdout="(C, D)\n", stderr="")

    monkeypatch.setattr(lean_executor.subprocess, "run", fake_run)

    project_dir = tmp_path / "engine"
    lean_file = tmp_path / "matchup.lean"
    result = lean_executor.run_lean_file(project_dir, lean_file)

    assert seen["cmd"] == ["lake", "env", "lean", "../matchup.lean"]
    assert seen["cwd"] == project_dir.resolve()
    assert seen["capture_output"] is True
    assert seen["text"] is True
    assert seen["check"] is False
    assert result.command == "lake env lean ../matchup.lean"
    assert result.returncode == 0
    assert result.stdout == "(C, D)\n"
    assert result.stderr == ""


def test_build_lean_project_invokes_lake_build(monkeypatch, tmp_path: Path) -> None:
    seen = {}

    def fake_run(cmd, cwd, capture_output, text, check):
        seen["cmd"] = cmd
        seen["cwd"] = cwd
        seen["capture_output"] = capture_output
        seen["text"] = text
        seen["check"] = check
        return SimpleNamespace(returncode=0, stdout="Build completed successfully.\n", stderr="")

    monkeypatch.setattr(lean_executor.subprocess, "run", fake_run)

    project_dir = tmp_path / "engine"
    result = lean_executor.build_lean_project(project_dir)

    assert seen["cmd"] == ["lake", "build", "PrisonersDilemma"]
    assert seen["cwd"] == project_dir.resolve()
    assert seen["capture_output"] is True
    assert seen["text"] is True
    assert seen["check"] is False
    assert result.command == "lake build PrisonersDilemma"
    assert result.returncode == 0
    assert result.stdout == "Build completed successfully.\n"
    assert result.stderr == ""

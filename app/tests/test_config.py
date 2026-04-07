from pathlib import Path

from pd_runner.config import load_paths


def test_load_paths_defaults_to_engine(monkeypatch) -> None:
    monkeypatch.delenv("PD_LEAN_ENGINE_DIR", raising=False)
    monkeypatch.delenv("PD_LEAN_CODE_DIR", raising=False)

    paths = load_paths()
    repo_root = Path(__file__).resolve().parents[2]

    assert paths.app_root == repo_root / "app"
    assert paths.lean_engine_dir == repo_root / "engine"
    assert paths.generated_lean_dir == repo_root / "app" / "generated" / "lean"
    assert paths.generated_logs_dir == repo_root / "app" / "generated" / "logs"


def test_load_paths_prefers_new_engine_override(monkeypatch, tmp_path: Path) -> None:
    old_override = tmp_path / "old-code-dir"
    new_override = tmp_path / "new-engine-dir"
    monkeypatch.setenv("PD_LEAN_CODE_DIR", str(old_override))
    monkeypatch.setenv("PD_LEAN_ENGINE_DIR", str(new_override))

    paths = load_paths()

    assert paths.lean_engine_dir == new_override.resolve()


def test_load_paths_falls_back_to_old_override(monkeypatch, tmp_path: Path) -> None:
    override = tmp_path / "legacy-code-dir"
    monkeypatch.delenv("PD_LEAN_ENGINE_DIR", raising=False)
    monkeypatch.setenv("PD_LEAN_CODE_DIR", str(override))

    paths = load_paths()

    assert paths.lean_engine_dir == override.resolve()
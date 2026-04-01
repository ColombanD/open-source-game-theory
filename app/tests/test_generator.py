from pathlib import Path

from pd_runner.lean.generator import write_matchup_lean_file


def test_write_matchup_lean_file(tmp_path: Path) -> None:
    out = write_matchup_lean_file(tmp_path, "cooperateBot", "defectBot")
    content = out.read_text(encoding="utf-8")

    assert out.exists()
    assert "#eval playActions Bot.cooperateBot Bot.defectBot" in content

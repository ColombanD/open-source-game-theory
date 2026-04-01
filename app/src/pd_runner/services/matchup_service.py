from __future__ import annotations

from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import run_lean_file
from pd_runner.lean.generator import write_matchup_lean_file
from pd_runner.lean.parser import parse_actions_from_stdout
from pd_runner.models import MatchupRequest, MatchupResult


def _cleanup_file(path: Path) -> None:
    try:
        path.unlink(missing_ok=True)
    except OSError:
        # Best effort cleanup only.
        pass


def run_matchup(request: MatchupRequest, keep_file: bool = True) -> MatchupResult:
    paths = load_paths()

    lean_file = write_matchup_lean_file(
        target_dir=paths.generated_lean_dir,
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        claim_left_action=request.claim_left_action,
        claim_right_action=request.claim_right_action,
    )

    exec_result = run_lean_file(paths.lean_code_dir, lean_file)
    if exec_result.returncode != 0:
        if not keep_file:
            _cleanup_file(lean_file)
        raise RuntimeError(
            "lean execution failed\n"
            f"command: {exec_result.command}\n"
            f"stderr:\n{exec_result.stderr}"
        )

    left_action, right_action = parse_actions_from_stdout(exec_result.stdout)

    if not keep_file:
        _cleanup_file(lean_file)

    return MatchupResult(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=left_action,
        right_action=right_action,
        lean_file=str(lean_file),
        command=exec_result.command,
    )

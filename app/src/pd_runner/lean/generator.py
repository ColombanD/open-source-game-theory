from __future__ import annotations

from datetime import datetime
from pathlib import Path

from pd_runner.lean.templates import matchup_eval_template


def validate_bot_name(name: str) -> None:
    # Keep this strict to avoid generating malformed Lean code.
    if not name:
        raise ValueError("bot name cannot be empty")
    if not name.replace("_", "").isalnum():
        raise ValueError(f"invalid bot name: {name}")


def write_matchup_lean_file(target_dir: Path, left_bot: str, right_bot: str) -> Path:
    validate_bot_name(left_bot)
    validate_bot_name(right_bot)

    target_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.utcnow().strftime("%Y%m%dT%H%M%S%f")
    path = target_dir / f"matchup_{left_bot}_{right_bot}_{timestamp}.lean"
    path.write_text(matchup_eval_template(left_bot, right_bot), encoding="utf-8")
    return path

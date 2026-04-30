from __future__ import annotations

import re
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path

from pd_runner.lean.templates import matchup_eval_template


@dataclass(frozen=True)
class GeneratedLeanFile:
    path: Path
    proof_theorem_used: str | None
    actions_are_swapped: bool
    result_kind: str = "concrete"
    witness: str | None = None


def validate_bot_name(name: str) -> None:
    # Keep this strict to avoid generating malformed Lean code.
    if not name:
        raise ValueError("bot name cannot be empty")
    if not re.fullmatch(r"[A-Za-z_]\w*(?::(\d+|\?))?", name):
        raise ValueError(f"invalid bot name: {name}")


def validate_action_name(name: str | None) -> None:
    if name is None:
        return
    if name not in {"C", "D"}:
        raise ValueError(f"invalid action: {name}. expected C or D")


def write_matchup_lean_file(
    target_dir: Path,
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> GeneratedLeanFile:
    validate_bot_name(left_bot)
    validate_bot_name(right_bot)
    validate_action_name(claim_left_action)
    validate_action_name(claim_right_action)
    if (claim_left_action is None) != (claim_right_action is None):
        raise ValueError("both claim actions must be provided together")

    target_dir.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%S%f")
    safe_left_bot = re.sub(r"[^A-Za-z0-9_]+", "_", left_bot)
    safe_right_bot = re.sub(r"[^A-Za-z0-9_]+", "_", right_bot)
    path = target_dir / f"matchup_{safe_left_bot}_{safe_right_bot}_{timestamp}.lean"
    script, proof_theorem_used, actions_are_swapped, result_kind, witness = matchup_eval_template(
        left_bot,
        right_bot,
        claim_left_action=claim_left_action,
        claim_right_action=claim_right_action,
    )
    path.write_text(
        script,
        encoding="utf-8",
    )
    return GeneratedLeanFile(
        path=path,
        proof_theorem_used=proof_theorem_used,
        actions_are_swapped=actions_are_swapped,
        result_kind=result_kind,
        witness=witness,
    )

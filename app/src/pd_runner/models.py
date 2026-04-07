from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class MatchupRequest:
    left_bot: str
    right_bot: str
    claim_left_action: str | None = None
    claim_right_action: str | None = None


@dataclass(frozen=True)
class MatchupResult:
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str
    lean_file: str
    command: str
    proof_theorem_used: str | None = None

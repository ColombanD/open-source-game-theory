from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class MatchupRequestSchema:
    left: str
    right: str


@dataclass(frozen=True)
class MatchupResponseSchema:
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str

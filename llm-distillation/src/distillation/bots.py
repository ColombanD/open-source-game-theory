"""Locate and read the Lean source code of the library bots.

The bot sources live in the main engine, one file per bot:

    <repo_root>/engine/PrisonersDilemma/Bots/<BotName>.lean

These are injected verbatim into the per-bot prompt so the model can read its
opponent's source code (the "open source / max transparency" setting).
"""

from __future__ import annotations

from pathlib import Path

# This file is <repo_root>/llm-distillation/src/distillation/bots.py, so the repo
# root is four parents up.
_REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_BOTS_DIR = _REPO_ROOT / "engine" / "PrisonersDilemma" / "Bots"


def load_bot_sources(
    bots: tuple[str, ...], bots_dir: Path = DEFAULT_BOTS_DIR
) -> dict[str, str]:
    """Read the Lean source for each bot name.

    Returns a mapping ``bot_name -> source_text``. Raises if any file is missing.
    """
    sources: dict[str, str] = {}
    for bot in bots:
        path = bots_dir / f"{bot}.lean"
        if not path.is_file():
            raise FileNotFoundError(f"No source file for bot {bot!r} at {path}")
        sources[bot] = path.read_text()
    return sources

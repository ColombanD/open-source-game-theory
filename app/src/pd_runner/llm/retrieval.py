"""M3: Retrieval of relevant existing theorems as few-shot context for the proof agent.

Strategy: structural/name match on bot names from the discovered theorem library.
Returns the full source of the most relevant theorem files.
"""

from __future__ import annotations

from pathlib import Path

from pd_runner.lean.templates import (
    _THEOREMS_DIR,
    _UNIVERSAL_OUTCOME_THEOREMS,
    _EXISTENTIAL_OUTCOME_THEOREMS,
)


def retrieve_few_shots(left_bot: str, right_bot: str, max_files: int = 4) -> list[tuple[str, str]]:
    """Return (filename, source) pairs for the most relevant existing theorem files.

    Ranking: files whose name matches one of the two bots come first; then any
    file that contains a theorem involving either bot name; then other files up
    to max_files.
    """
    theorems_dir = _THEOREMS_DIR
    if not theorems_dir.exists():
        return []

    target_names = {left_bot.lower(), right_bot.lower()}

    def _score(path: Path) -> int:
        stem = path.stem.lower()
        if stem in target_names:
            return 2
        content = path.read_text(encoding="utf-8").lower()
        if any(name in content for name in target_names):
            return 1
        return 0

    candidates = sorted(
        theorems_dir.glob("*.lean"),
        key=lambda p: (-_score(p), p.name),
    )

    results: list[tuple[str, str]] = []
    for path in candidates:
        if len(results) >= max_files:
            break
        # Skip files that scored 0 — not relevant enough unless we have few options
        if _score(path) == 0 and len(results) >= 2:
            break
        try:
            results.append((path.name, path.read_text(encoding="utf-8")))
        except OSError:
            continue

    return results


def list_known_outcome_theorems(left_bot: str, right_bot: str) -> str:
    """Return a short summary of any already-proven outcome theorems for this pair."""
    target = {left_bot, right_bot}
    lines: list[str] = []

    for thm in _UNIVERSAL_OUTCOME_THEOREMS:
        bots = {thm.left_bot.name, thm.right_bot.name}
        if bots & target:
            lines.append(
                f"  {thm.name} (module {thm.module}): "
                f"{thm.left_bot.existential_lean()} vs {thm.right_bot.existential_lean()} "
                f"→ ({thm.left_action}, {thm.right_action})"
            )

    for thm in _EXISTENTIAL_OUTCOME_THEOREMS:
        bots = {thm.left_bot.name, thm.right_bot.name}
        if bots & target:
            lines.append(
                f"  {thm.name} (module {thm.module}, existential): "
                f"{thm.left_bot.existential_lean()} vs {thm.right_bot.existential_lean()} "
                f"→ ({thm.left_action}, {thm.right_action})"
            )

    if not lines:
        return "None found."
    return "\n".join(lines)

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


def retrieve_few_shots(left_bot: str, right_bot: str, max_files: int = 4, exclude_bots: set[str] | None = None) -> list[tuple[str, str]]:
    """Return (filename, source) pairs for the most relevant existing theorem files.

    Ranking: files whose name matches one of the two bots come first; then any
    file that contains a theorem involving either bot name; then other files up
    to max_files.
    """
    theorems_dir = _THEOREMS_DIR
    if not theorems_dir.exists():
        return []

    target_names = {left_bot.lower(), right_bot.lower()}
    excluded = {b.lower() for b in exclude_bots} if exclude_bots else set()

    def _mentions_excluded(path: Path) -> bool:
        """True if the file is the dedicated file for an excluded bot.

        We only filter on filename stem — a file is "about" an excluded bot if
        it is named after it (e.g. `Theorems/CupodBot.lean`). Files that merely
        mention a target bot in passing are kept, since the proof for a pair
        (A, B) is, by repo convention, located in `Theorems/A.lean` or
        `Theorems/B.lean`, not in unrelated bots' files.
        """
        return path.stem.lower() in excluded

    def _score(path: Path) -> int:
        stem = path.stem.lower()
        if stem in target_names:
            return 2
        content = path.read_text(encoding="utf-8").lower()
        if any(name in content for name in target_names):
            return 1
        return 0

    candidates = sorted(
        (p for p in theorems_dir.glob("*.lean") if not _mentions_excluded(p)),
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


def list_known_outcome_theorems(left_bot: str, right_bot: str, exclude_bots: set[str] | None = None) -> str:
    """Return a short summary of already-proven outcome theorems involving these bots.

    Leak prevention: theorems whose pair *exactly matches* the target pair are
    omitted (that would print the answer directly). Theorems involving only one
    of the target bots are kept — they give useful prior signal (e.g. how the
    target behaves against a different opponent) without revealing the queried
    outcome.
    """
    target = {left_bot, right_bot}
    excluded_pairs: set[frozenset[str]] = set()
    if exclude_bots is not None:
        # The "answer" we must hide is a theorem about the exact target pair.
        excluded_pairs.add(frozenset(target))
    lines: list[str] = []

    def _emit(thm, suffix: str) -> None:
        bots = {thm.left_bot.name, thm.right_bot.name}
        if frozenset(bots) in excluded_pairs:
            return
        if not (bots & target):
            return
        lines.append(
            f"  {thm.name} (module {thm.module}{suffix}): "
            f"{thm.left_bot.existential_lean()} vs {thm.right_bot.existential_lean()} "
            f"→ ({thm.left_action}, {thm.right_action})"
        )

    for thm in _UNIVERSAL_OUTCOME_THEOREMS:
        _emit(thm, "")
    for thm in _EXISTENTIAL_OUTCOME_THEOREMS:
        _emit(thm, ", existential")

    if not lines:
        return "None found."
    return "\n".join(lines)

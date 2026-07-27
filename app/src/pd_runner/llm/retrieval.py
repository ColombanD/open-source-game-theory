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

    def _file_bots(path: Path) -> set[str]:
        """The bots a file is dedicated to, from its path.

        Three layouts coexist: legacy per-bot files (`Theorems/CupodBot.lean` →
        {cupodbot}), sharded per-pair files (`Theorems/JustBot/vs_DBot.lean` →
        {justbot, dbot}), and dir-local helpers (`Theorems/JustBot/Helpers.lean`
        → {justbot}).
        """
        stem = path.stem.lower()
        if stem.startswith("vs_"):
            return {path.parent.name.lower(), stem[3:]}
        if stem == "helpers" and path.parent != theorems_dir:
            return {path.parent.name.lower()}
        return {stem}

    def _mentions_excluded(path: Path) -> bool:
        """True if the file is dedicated to an excluded bot (filename/dir based).

        Files that merely mention a target bot in passing are kept, since the
        proof for a pair (A, B) is, by repo convention, located in a file named
        for A or B, not in unrelated bots' files.
        """
        return bool(_file_bots(path) & excluded)

    def _score(path: Path) -> int:
        if _file_bots(path) & target_names:
            return 2
        content = path.read_text(encoding="utf-8").lower()
        if any(name in content for name in target_names):
            return 1
        return 0

    # Include the LLM-generated proof files as few-shot candidates too: the pipeline's
    # own past successes are often the best examples for a new pair. `LlmLemmas.lean`
    # is excluded here — it is the agent's derived-rule library, embedded verbatim in
    # the system prompt rather than competing for few-shot slots.
    pool = [
        p
        for pattern in ("*.lean", "LlmGenerations/*.lean", "*/vs_*.lean", "*/Helpers.lean")
        for p in theorems_dir.glob(pattern)
        if p.stem != "LlmLemmas" and not _mentions_excluded(p)
    ]
    candidates = sorted(pool, key=lambda p: (-_score(p), p.name))

    results: list[tuple[str, str]] = []
    for path in candidates:
        if len(results) >= max_files:
            break
        # Skip files that scored 0 — not relevant enough unless we have few options
        if _score(path) == 0 and len(results) >= 2:
            break
        try:
            content = path.read_text(encoding="utf-8")
        except OSError:
            continue
        # Skip umbrella/index files (pure import lists) — no proof content to learn from.
        if "theorem" not in content:
            continue
        # Label with the Theorems-relative path: per-pair files share basenames
        # across bot directories (every dir has a vs_DBot.lean eventually).
        results.append((str(path.relative_to(theorems_dir)), content))

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

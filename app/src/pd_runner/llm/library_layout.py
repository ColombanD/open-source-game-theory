"""The single implementation of the Theorems/ path-layout rules.

Both the few-shot retriever and the `read_library_file` leak filter need to
know which bots a library file is *dedicated to*. That logic used to exist in
two near-verbatim copies (retrieval.py and tools.py) — divergence there
silently breaks leak prevention, so it lives here once.
"""

from __future__ import annotations

from pathlib import Path


def file_bots(path: Path, theorems_dir: Path) -> set[str]:
    """The (lowercased) bot names a theorem file is dedicated to, from its path.

    Three layouts coexist:
      - legacy per-bot file:  Theorems/CupodBot.lean        -> {cupodbot}
      - sharded per-pair:     Theorems/JustBot/vs_DBot.lean -> {justbot, dbot}
      - dir-local helpers:    Theorems/JustBot/Helpers.lean -> {justbot}

    Files that merely *mention* a bot are not dedicated to it — dedication is
    purely path-based, which is exactly what the leak filter and the
    path-dedication retrieval bonus both want.
    """
    stem = path.stem.lower()
    if stem.startswith("vs_"):
        return {path.parent.name.lower(), stem[3:]}
    if stem == "helpers" and path.parent != theorems_dir:
        return {path.parent.name.lower()}
    return {stem}

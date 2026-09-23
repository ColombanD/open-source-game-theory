"""Declaration search over the engine library — the closed-world analogue of
LeanSearch.

The proof agent often knows roughly WHAT it needs ("the OBot floor census",
"something about tailTo") but not WHERE it lives; `read_library_file` requires
an exact path. `search_declarations` greps every declaration in the engine and
returns name + location + signature, so the agent can find machinery by name
or by statement content and then fetch the full file.

Leak prevention mirrors `read_library_file`: files DEDICATED to a hidden bot
(path-based, `library_layout.file_bots`) are skipped entirely.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.llm.library_layout import file_bots

_DECL_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(theorem|lemma|def|abbrev|inductive|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?.]*)"
)

_MAX_SIG_LINES = 6
_MAX_SIG_CHARS = 400


@dataclass(frozen=True)
class DeclMatch:
    name: str
    kind: str
    relative_path: str   # relative to PrisonersDilemma/
    line: int            # 1-based
    signature: str
    name_hit: bool       # matched on the name (ranks above signature-only hits)


def _extract_signature(lines: list[str], start: int) -> str:
    """The declaration text from its first line up to `:=` (or a few lines)."""
    collected: list[str] = []
    for i in range(start, min(start + _MAX_SIG_LINES, len(lines))):
        line = lines[i]
        cut = line.find(":=")
        if cut != -1:
            collected.append(line[:cut].rstrip())
            break
        collected.append(line.rstrip())
    sig = "\n".join(collected).strip()
    if len(sig) > _MAX_SIG_CHARS:
        sig = sig[:_MAX_SIG_CHARS] + " …"
    return sig


def search_declarations(
    pattern: str,
    *,
    hidden_bots: frozenset[str] = frozenset(),
    max_results: int = 30,
    engine_pd_dir: Path | None = None,
) -> list[DeclMatch]:
    """All engine declarations whose name or signature matches `pattern`.

    `pattern` is treated as a case-insensitive regex when it compiles, else as
    a literal substring. Name hits rank before signature-only hits; ties keep
    file order. Research/ spikes are excluded (not in the build targets).
    """
    root = engine_pd_dir or (load_paths().lean_engine_dir / "PrisonersDilemma")
    try:
        needle = re.compile(pattern, re.IGNORECASE)
    except re.error:
        needle = re.compile(re.escape(pattern), re.IGNORECASE)

    excluded = {b.lower() for b in hidden_bots}
    theorems_dir = root / "Theorems"
    name_hits: list[DeclMatch] = []
    sig_hits: list[DeclMatch] = []

    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root).as_posix()
        if rel.startswith("Research/"):
            continue
        if excluded and (file_bots(path, theorems_dir) & excluded):
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for i, line in enumerate(lines):
            m = _DECL_LINE_RE.match(line)
            if m is None:
                continue
            kind, name = m.group(1), m.group(2)
            signature = _extract_signature(lines, i)
            if needle.search(name):
                name_hits.append(DeclMatch(name, kind, rel, i + 1, signature, True))
            elif needle.search(signature):
                sig_hits.append(DeclMatch(name, kind, rel, i + 1, signature, False))
            if len(name_hits) >= max_results:
                break
        if len(name_hits) >= max_results:
            break

    return (name_hits + sig_hits)[:max_results]


def format_matches(matches: list[DeclMatch], pattern: str, max_results: int = 30) -> str:
    if not matches:
        return (
            f"No declarations matching {pattern!r} found in the engine library. "
            "Try a shorter or different pattern (case-insensitive; regex supported)."
        )
    parts: list[str] = []
    for m in matches:
        parts.append(f"{m.kind} `{m.name}` — {m.relative_path}:{m.line}\n    {m.signature}")
    listing = "\n\n".join(parts)
    note = ""
    if len(matches) >= max_results:
        note = f"\n\n(showing the first {max_results} matches — narrow the pattern for more precision)"
    return (
        f"{len(matches)} declaration(s) matching {pattern!r} "
        "(fetch any full file with read_library_file):\n\n" + listing + note
    )

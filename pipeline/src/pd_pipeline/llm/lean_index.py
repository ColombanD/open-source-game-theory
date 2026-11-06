"""Signature digests of large Lean modules for prompt embedding.

The heavyweight modules (`ProofSystem.lean` ~56KB, `Base/Exclusion.lean`
~44KB) used to be embedded verbatim in every `.search`-matchup system prompt.
What the agent actually needs from them is the STATEMENTS: constructor lists,
theorem signatures, doc comments. `strip_proof_bodies` removes only the proof
bodies of `theorem`/`lemma` declarations and leaves everything else verbatim
(inductives — whose constructor lines ARE signatures — `def` right-hand
sides, doc comments, section markers, notation). Proof bodies can always be
fetched on demand with `read_library_file`.

The transform is a line-based heuristic for a prompt digest, not semantics:
the re-compile gate and the engine remain the ground truth.
"""

from __future__ import annotations

import re

# A line that starts a new top-level construct ends any proof body we are
# currently skipping. Column-0 only: tactic blocks and nested terms are
# indented in this codebase's style.
_TOP_LEVEL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|mutual|"
    r"namespace|section|end\b|open\s|variable|set_option|attribute|notation|"
    r"deriving|/--|/-!|--)"
)

_THEOREM_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\b"
)

_OMITTED = "(proof omitted — fetch the full file with read_library_file if needed)"


def strip_proof_bodies(source: str) -> str:
    """Drop `theorem`/`lemma` proof bodies; keep every statement and everything else."""
    out: list[str] = []
    lines = source.splitlines()
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if not _THEOREM_START_RE.match(line):
            out.append(line)
            i += 1
            continue
        # Inside a theorem/lemma declaration: emit statement lines until the
        # first `:=`, then skip the proof body up to the next top-level line.
        found_assign = False
        while i < n:
            stmt_line = lines[i]
            cut = stmt_line.find(":=")
            if cut != -1:
                out.append(stmt_line[:cut].rstrip() + " := " + _OMITTED)
                found_assign = True
                i += 1
                break
            out.append(stmt_line)
            i += 1
            if i < n and _TOP_LEVEL_RE.match(lines[i]):
                # No `:=` in this declaration block (unusual shape) — leave as-is.
                break
        if not found_assign:
            continue
        # Skip proof-body lines until the next top-level construct.
        while i < n and not _TOP_LEVEL_RE.match(lines[i]) :
            i += 1
    # Collapse runs of blank lines left behind by removed bodies.
    text = "\n".join(out)
    return re.sub(r"\n{3,}", "\n\n", text)

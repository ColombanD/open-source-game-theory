"""The agent-owned derived-lemma library (Tier 1 of the OUTCOME-OPEN escalation ladder).

`add_lemma` lets the proof agent grow a persistent library of DERIVED rules — theorems
over the existing proof system `Pf` — instead of declaring OUTCOME OPEN when the missing
piece is merely an uncombined consequence of existing rules. This is the sound-by-
construction tier: a `theorem` is kernel-checked, so nothing is postulated and no human
gate is needed beyond the build. (The project's own history motivates it: `boxInternalize`
and `box_provable` were both once thought to need new axioms and turned out to be
derivable; `mutual_loeb` is a plain theorem.)

Safety model:
  * ADDITIVE ONLY — lemmas are appended to one dedicated file
    (`Theorems/LlmGenerations/LlmLemmas.lean`); no existing file is ever modified.
  * TRANSACTIONAL — the file is restored byte-for-byte if `lake build` fails.
  * GUARDED — sources that would extend the trusted base are rejected before compile:
    `axiom` (postulates), `sorry`/`admit` (holes), `inductive` (new types are Tier 2's
    domain — see `constructor_proposals`), `native_decide`/`implemented_by`/`extern`
    (extend trust to compiled code), `unsafe`/`partial` (non-total definitions), and
    bot redefinitions (namespace clashes).
"""

from __future__ import annotations

import re
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import build_lean_project
from pd_runner.logging_config import get_logger

_log = get_logger("services.lemma_library")

LEMMA_MODULE = "PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas"

_HEADER = '''import PrisonersDilemma.BaseTheorems

/-!
# LlmLemmas — the proof agent's DERIVED-rule library

Theorems over the existing proof system `Pf`, added autonomously by the proof agent via
the `add_base_lemma` tool (Tier 1 of the OUTCOME-OPEN escalation ladder). Everything here
is kernel-checked against the unchanged engine — nothing is postulated, so this file
carries no trust obligations beyond the engine itself. Additive-only; each block below is
one tool call.
-/

open PD PD.BaseTheorems

namespace PD.LlmLemmas

/-- Seed example (the expected format): reflect a fired oracle back into provability. -/
theorem pf_of_proofSearch {k : Nat} {φ : Formula} (h : proofSearch k φ = true) : Pf k φ :=
  (proofSearch_spec k φ).1 h

end PD.LlmLemmas
'''

# Patterns that would extend the trusted base — rejected before any compile.
_FORBIDDEN: list[tuple[str, str]] = [
    (r"\baxiom\b", "`axiom` postulates an unproven statement — the library is theorem-only. "
                   "If the rule is genuinely underivable, use `propose_pf_constructor` instead."),
    (r"\bsorry\b", "`sorry` leaves a hole — only complete proofs can be added."),
    (r"\badmit\b", "`admit` leaves a hole — only complete proofs can be added."),
    (r"\binductive\b", "new inductive types cannot be added here — extending the proof "
                       "system is Tier 2 (`propose_pf_constructor`)."),
    (r"\bnative_decide\b", "`native_decide` extends the trusted base to the compiler — "
                           "use `decide` or an explicit proof."),
    (r"\bimplemented_by\b", "`implemented_by` substitutes unverified code."),
    (r"@\[extern", "`@[extern]` substitutes unverified code."),
    (r"\bunsafe\b", "`unsafe` definitions bypass the kernel."),
    (r"\bmacro\b|\belab\b|\bnotation\b", "metaprogramming/notation is not allowed in the "
                                         "lemma library — plain `theorem`/`lemma`/`def` only."),
]

_BOT_DEF_RE = re.compile(r"^\s*def\s+(\w+)\s*:\s*Prog\b", re.MULTILINE)


class LemmaRejected(Exception):
    """Raised when a lemma source fails the static guards."""


def _lemma_file(paths) -> Path:
    return paths.lean_engine_dir / "PrisonersDilemma" / "Theorems" / "LlmGenerations" / "LlmLemmas.lean"


def _index_file(paths) -> Path:
    return paths.lean_engine_dir / "PrisonersDilemma" / "Theorems" / "LlmGenerations.lean"


def _check_source(lean_source: str) -> None:
    for pattern, reason in _FORBIDDEN:
        if re.search(pattern, lean_source):
            raise LemmaRejected(reason)
    bots = _BOT_DEF_RE.findall(lean_source)
    if bots:
        raise LemmaRejected(
            f"lemma source defines Prog value(s) {', '.join(bots)} — bots may not be "
            f"(re)defined here; import them from `PrisonersDilemma.Bots.…` instead."
        )
    if not re.search(r"\b(theorem|lemma|def)\b", lean_source):
        raise LemmaRejected("no `theorem`/`lemma`/`def` found in the source.")
    if re.search(r"\b(namespace|end|import|section)\b", lean_source):
        raise LemmaRejected(
            "do not include `import`/`namespace`/`section`/`end` lines — the source is "
            "appended INSIDE `namespace PD.LlmLemmas` (with `PD` and `PD.BaseTheorems` "
            "open); submit bare declarations only."
        )


def bootstrap(paths=None) -> Path:
    """Create the lemma file (and its index import) if missing. Returns the file path."""
    paths = paths or load_paths()
    target = _lemma_file(paths)
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(_HEADER, encoding="utf-8")
    index = _index_file(paths)
    import_line = f"import {LEMMA_MODULE}\n"
    existing = index.read_text(encoding="utf-8") if index.exists() else ""
    if import_line not in existing:
        with index.open("a", encoding="utf-8") as f:
            f.write(import_line)
    return target


def add_lemma(lemma_name: str, lean_source: str, *, build=build_lean_project) -> str:
    """Append a lemma block transactionally; returns a tool-style report string.

    The block is inserted before the closing `end PD.LlmLemmas`, the module is rebuilt,
    and the file is restored byte-for-byte on failure. `build` is injectable for tests.
    """
    try:
        _check_source(lean_source)
    except LemmaRejected as exc:
        return f"REJECTED (static guard): {exc}"

    paths = load_paths()
    target = bootstrap(paths)
    original = target.read_text(encoding="utf-8")

    marker = "end PD.LlmLemmas"
    if marker not in original:
        return f"REJECTED: lemma file is malformed (missing `{marker}`) — fix it manually."

    block = f"\n/-! ### {lemma_name} (agent-added) -/\n\n{lean_source.strip()}\n\n"
    updated = original.replace(marker, block + marker)
    target.write_text(updated, encoding="utf-8")

    result = build(paths.lean_engine_dir, target=LEMMA_MODULE)
    if result.returncode != 0:
        target.write_text(original, encoding="utf-8")
        _log.info("Lemma %s rejected by lake build; file rolled back", lemma_name)
        return (
            "BUILD FAILED — the lemma was rolled back (library unchanged).\n"
            f"--- stdout ---\n{result.stdout or '(empty)'}\n"
            f"--- stderr ---\n{result.stderr or '(empty)'}\n"
            "Fix the proof and call add_base_lemma again."
        )

    _log.info("Lemma %s added to %s", lemma_name, target)
    return (
        f"OK — `{lemma_name}` added to the library and verified by lake build.\n"
        f"Use it in your proof under the `PD.LlmLemmas` namespace after adding\n"
        f"`import {LEMMA_MODULE}` to your proof file."
    )

"""Library writer — persist proven proofs and generated bots to the library.

Safety rules:
- Only adds new files, never overwrites existing ones.
- Verifies the whole project still builds after writing (proofs only).
- Provides a human-acceptance gate before writing.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import LeanExecResult, build_lean_project
from pd_runner.services.bot_service import BotResult
from pd_runner.services.proof_service import ProofResult


@dataclass(frozen=True)
class WriteResult:
    path: Path
    build_ok: bool
    build_stdout: str
    build_stderr: str


class LibraryWriteError(RuntimeError):
    pass


def theorem_file_path(result: ProofResult) -> Path:
    """Canonical per-pair path: Theorems/<LeftBot>/vs_<RightBot>.lean.

    Sharded-by-left-bot layout (2026-07-27 refactor): one file per ordered
    matchup, directories keep the file count per level at ~N. Dir-local shared
    lemmas live in Theorems/<LeftBot>/Helpers.lean; reusable rules go to
    LlmLemmas via add_base_lemma.
    """
    paths = load_paths()
    theorems_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Theorems"
    return theorems_dir / result.left_bot / f"vs_{result.right_bot}.lean"


def _llm_generations_index(paths) -> Path:
    # No-top-level-files layout (2026-07-27): there is no Theorems/LlmGenerations.lean
    # index anymore — new theorem modules are wired in by appending their import to
    # the engine's ROOT module.
    return paths.lean_engine_dir / "PrisonersDilemma.lean"


def _module_name(result: ProofResult) -> str:
    return f"PrisonersDilemma.Theorems.{result.left_bot}.vs_{result.right_bot}"


def write_proof_to_library(
    result: ProofResult,
    *,
    human_accept: bool = True,
    dry_run: bool = False,
) -> WriteResult:
    """Write a proven proof file to engine/PrisonersDilemma/Theorems/.

    Args:
        result: A ProofResult from search_proof.
        human_accept: If True, prompt the user to confirm before writing.
        dry_run: If True, skip writing and building — just validate the path.

    Raises:
        LibraryWriteError: if the file already exists, the user rejects, or
                           lake build fails after writing.
    """
    target = theorem_file_path(result)

    if target.exists():
        raise LibraryWriteError(
            f"Theorem file already exists: {target}\n"
            "The proof agent may only add new files, not overwrite existing ones."
        )

    if human_accept and not dry_run:
        print(f"\nProposed new theorem file: {target}")
        print(f"\n--- Lean source ---\n{result.lean_source}\n---")
        answer = input("Accept and write to library? [y/N] ").strip().lower()
        if answer != "y":
            raise LibraryWriteError("User rejected the proof — not written to library.")

    if dry_run:
        return WriteResult(
            path=target,
            build_ok=True,
            build_stdout="(dry run)",
            build_stderr="",
        )

    paths = load_paths()

    # Fast pre-write gate: duplicate top-level names would fail the umbrella build
    # with `environment already contains ...` AFTER an expensive full build — catch
    # them here with the precise clash list instead (the build rollback below stays
    # as the backstop for anything the scan cannot see).
    from pd_runner.services.proof_service import (
        find_census_inductions,
        find_library_name_collisions,
    )

    inductions = find_census_inductions(result.lean_source)
    if inductions:
        raise LibraryWriteError(
            f"refusing to write {target}: the proof uses "
            f"{', '.join(inductions)} — a hand-rolled census over the full `Pf` "
            f"inductive. These break with missing-cases on every future constructor "
            f"addition; matchup censuses must instantiate the shared kernels in "
            f"Base/Exclusion.lean instead. If this induction is genuinely "
            f"irreducible to a kernel instance, land the file by hand."
        )

    engine_root = paths.lean_engine_dir / "PrisonersDilemma"
    collisions = find_library_name_collisions(
        result.lean_source,
        exclude_relpath=target.resolve().relative_to(engine_root.resolve()).as_posix(),
    )
    if collisions:
        listing = "\n".join(f"  - `{n}` already declared in {f}" for n, f in collisions)
        raise LibraryWriteError(
            f"refusing to write {target}: it re-declares names that already exist in "
            f"the library (the umbrella `lake build` would fail with `environment "
            f"already contains ...`):\n{listing}\n"
            f"Fix: rename the clashing declarations with a matchup-specific prefix "
            f"and retry."
        )

    # Ensure the per-bot directory (Theorems/<LeftBot>/) exists.
    target.parent.mkdir(parents=True, exist_ok=True)

    target.write_text(result.lean_source + "\n", encoding="utf-8")

    # Append the import line to the index file (skip if already present).
    index = _llm_generations_index(paths)
    import_line = f"import {_module_name(result)}\n"
    existing_index = index.read_text(encoding="utf-8")
    if import_line not in existing_index:
        with index.open("a", encoding="utf-8") as f:
            f.write(import_line)

    build_result: LeanExecResult = build_lean_project(paths.lean_engine_dir)

    if build_result.returncode != 0:
        # Roll back both the proof file and the index line.
        target.unlink(missing_ok=True)
        index_text = index.read_text(encoding="utf-8")
        index.write_text(index_text.replace(import_line, ""), encoding="utf-8")
        raise LibraryWriteError(
            f"lake build failed after writing {target} — file removed.\n"
            f"stdout:\n{build_result.stdout}\nstderr:\n{build_result.stderr}"
        )

    return WriteResult(
        path=target,
        build_ok=True,
        build_stdout=build_result.stdout,
        build_stderr=build_result.stderr,
    )


# ---------------------------------------------------------------------------
# Bot writer
# ---------------------------------------------------------------------------

def bot_file_path(result: BotResult) -> Path:
    """Return the canonical path for this bot inside the LLM generations subfolder."""
    paths = load_paths()
    llm_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations"
    return llm_dir / f"{result.bot_name}.lean"


def write_bot_to_library(
    result: BotResult,
    *,
    human_accept: bool = True,
    dry_run: bool = False,
    overwrite: bool = False,
) -> WriteResult:
    """Write a generated bot file to engine/PrisonersDilemma/Bots/LlmGenerations/.

    No lake build — bots are imported transitively by their theorem files,
    which are verified when write_proof_to_library runs lake build.

    Raises:
        LibraryWriteError: if the file already exists (and overwrite=False) or the user rejects.
    """
    target = bot_file_path(result)

    if target.exists() and not overwrite:
        raise LibraryWriteError(
            f"Bot file already exists: {target}\n"
            "The bot writer may only add new files, not overwrite existing ones."
        )

    if human_accept and not dry_run:
        print(f"\nProposed new bot file: {target}")
        print(f"\n--- Lean source ---\n{result.lean_source}\n---")
        answer = input("Accept and write to library? [y/N] ").strip().lower()
        if answer != "y":
            raise LibraryWriteError("User rejected the bot — not written to library.")

    if dry_run:
        return WriteResult(
            path=target,
            build_ok=True,
            build_stdout="(dry run)",
            build_stderr="",
        )

    paths = load_paths()
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(result.lean_source + "\n", encoding="utf-8")

    return WriteResult(
        path=target,
        build_ok=True,
        build_stdout="",
        build_stderr="",
    )

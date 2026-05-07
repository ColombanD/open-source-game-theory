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
    """Return the canonical path for this proof inside the LLM generations subfolder."""
    paths = load_paths()
    llm_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Theorems" / "LlmGenerations"
    filename = f"outcome_{result.left_bot}_vs_{result.right_bot}.lean"
    return llm_dir / filename


def _llm_generations_index(paths) -> Path:
    return paths.lean_engine_dir / "PrisonersDilemma" / "Theorems" / "LlmGenerations.lean"


def _module_name(result: ProofResult) -> str:
    return f"PrisonersDilemma.Theorems.LlmGenerations.outcome_{result.left_bot}_vs_{result.right_bot}"


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

    # Ensure the LlmGenerations directory exists.
    target.parent.mkdir(parents=True, exist_ok=True)

    target.write_text(result.lean_source + "\n", encoding="utf-8")

    # Append the import line to the index file.
    index = _llm_generations_index(paths)
    import_line = f"import {_module_name(result)}\n"
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


def _bot_llm_generations_index(paths) -> Path:
    return paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations.lean"


def _bot_module_name(result: BotResult) -> str:
    return f"PrisonersDilemma.Bots.LlmGenerations.{result.bot_name}"


def write_bot_to_library(
    result: BotResult,
    *,
    human_accept: bool = True,
    dry_run: bool = False,
) -> WriteResult:
    """Write a generated bot file to engine/PrisonersDilemma/Bots/LlmGenerations/.

    Does NOT run lake build — bots are not imported by the root module.
    The import is appended to Bots/LlmGenerations.lean so the proof agent
    can import the bot when writing outcome theorems.

    Raises:
        LibraryWriteError: if the file already exists or the user rejects.
    """
    target = bot_file_path(result)

    if target.exists():
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

    index = _bot_llm_generations_index(paths)
    import_line = f"import {_bot_module_name(result)}\n"
    with index.open("a", encoding="utf-8") as f:
        f.write(import_line)

    return WriteResult(
        path=target,
        build_ok=True,
        build_stdout="",
        build_stderr="",
    )

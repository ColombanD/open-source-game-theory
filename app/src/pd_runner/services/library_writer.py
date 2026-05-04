"""M6: Library writer — persist a proven proof to the theorem library.

Safety rules:
- Only adds new files, never overwrites existing ones.
- Verifies the whole project still builds after writing.
- Provides a human-acceptance gate before writing.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.lean.executor import LeanExecResult, build_lean_project
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
    """Return the canonical path for this proof inside the theorem library."""
    paths = load_paths()
    theorems_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Theorems"
    filename = f"outcome_{result.left_bot}_vs_{result.right_bot}.lean"
    return theorems_dir / filename


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

    target.write_text(result.lean_source + "\n", encoding="utf-8")

    paths = load_paths()
    build_result: LeanExecResult = build_lean_project(paths.lean_engine_dir)

    if build_result.returncode != 0:
        # Roll back — the proof broke the build.
        target.unlink(missing_ok=True)
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

from __future__ import annotations

import subprocess
import shlex
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class LeanExecResult:
    command: str
    returncode: int
    stdout: str
    stderr: str


def run_lean_file(lean_project_dir: Path, lean_file: Path) -> LeanExecResult:
    lean_project_dir = lean_project_dir.resolve()
    lean_file = lean_file.resolve()
    try:
        lean_file_arg = lean_file.relative_to(lean_project_dir)
    except ValueError:
        lean_file_arg = Path("..") / lean_file.relative_to(lean_project_dir.parent)

    cmd = ["lake", "env", "lean", str(lean_file_arg)]
    proc = subprocess.run(
        cmd,
        cwd=lean_project_dir,
        capture_output=True,
        text=True,
        check=False,
    )
    return LeanExecResult(
        command=shlex.join(cmd),
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


def run_lean_proof_file(lean_project_dir: Path, lean_file: Path) -> LeanExecResult:
    """Run a single Lean file against the already-built project (no lake build).

    Use this for the per-iteration proof check inside the agentic loop —
    it avoids the multi-second lake build cost on every attempt.
    The project must have been built at least once before calling this.
    """
    return run_lean_file(lean_project_dir, lean_file)


def build_lean_project(lean_project_dir: Path, target: str = "PrisonersDilemma") -> LeanExecResult:
    lean_project_dir = lean_project_dir.resolve()
    cmd = ["lake", "build", target]
    proc = subprocess.run(
        cmd,
        cwd=lean_project_dir,
        capture_output=True,
        text=True,
        check=False,
    )
    return LeanExecResult(
        command=shlex.join(cmd),
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )

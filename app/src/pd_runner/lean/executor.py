from __future__ import annotations

import subprocess
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class LeanExecResult:
    command: str
    returncode: int
    stdout: str
    stderr: str


def run_lean_file(lean_project_dir: Path, lean_file: Path) -> LeanExecResult:
    cmd = ["lake", "env", "lean", str(lean_file)]
    proc = subprocess.run(
        cmd,
        cwd=lean_project_dir,
        capture_output=True,
        text=True,
        check=False,
    )
    return LeanExecResult(
        command=" ".join(cmd),
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )

"""Claude tool definitions and implementations for the proof-search agent.

Two tools are exposed to the agent:
  - run_lean_proof: write a candidate proof to a temp file and run lake env lean
  - read_library_file: read any file under engine/PrisonersDilemma/ for few-shot context
"""

from __future__ import annotations

import tempfile
from pathlib import Path
from typing import Any

from pd_runner.config import load_paths
from pd_runner.lean.executor import run_lean_proof_file


# ---------------------------------------------------------------------------
# Claude tool schemas (passed to the Anthropic messages API via `tools=`)
# ---------------------------------------------------------------------------

LEAN_TOOLS: list[dict[str, Any]] = [
    {
        "name": "run_lean_proof",
        "description": (
            "Write a Lean 4 proof attempt to a temporary file and check it with `lake env lean`. "
            "Returns the Lean compiler stdout, stderr, and exit code. "
            "An exit code of 0 with no errors in stderr means the proof is correct. "
            "Use this tool to iteratively refine a proof based on compiler feedback."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "lean_source": {
                    "type": "string",
                    "description": (
                        "Complete Lean 4 source for the theorem file, including all imports, "
                        "namespace declarations, and the theorem with its proof."
                    ),
                },
                "filename_hint": {
                    "type": "string",
                    "description": (
                        "Optional short filename (without .lean extension) used for the temp file, "
                        "e.g. 'MyBot_vs_OtherBot'. Defaults to 'proof_attempt'."
                    ),
                },
            },
            "required": ["lean_source"],
        },
    },
    {
        "name": "read_library_file",
        "description": (
            "Read any file under engine/PrisonersDilemma/ (Bots/, Theorems/, or root files). "
            "Use this to fetch existing theorems as few-shot proof examples or to inspect a bot's "
            "definition before writing a proof about it."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "relative_path": {
                    "type": "string",
                    "description": (
                        "Path relative to engine/PrisonersDilemma/, e.g. "
                        "'Theorems/CooperateBot.lean' or 'Bots/DefectBot.lean'."
                    ),
                }
            },
            "required": ["relative_path"],
        },
    },
]


# ---------------------------------------------------------------------------
# Tool implementations
# ---------------------------------------------------------------------------

def _run_lean_proof(lean_source: str, filename_hint: str = "proof_attempt") -> str:
    paths = load_paths()
    lean_dir = paths.lean_engine_dir

    safe_hint = "".join(c if c.isalnum() or c in "_-" else "_" for c in filename_hint)
    prefix = f"pd_proof_{safe_hint}_"

    # Write to a temp file inside the engine dir so lake env lean can resolve imports.
    # The file is cleaned up after the check.
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix=prefix,
        dir=lean_dir,
        delete=False,
    ) as f:
        f.write(lean_source)
        tmp_path = Path(f.name)

    try:
        result = run_lean_proof_file(lean_dir, tmp_path)
    finally:
        tmp_path.unlink(missing_ok=True)

    lines = [
        f"exit_code: {result.returncode}",
        "--- stdout ---",
        result.stdout or "(empty)",
        "--- stderr ---",
        result.stderr or "(empty)",
    ]
    return "\n".join(lines)


def _read_library_file(relative_path: str) -> str:
    paths = load_paths()
    target = (paths.lean_engine_dir / "PrisonersDilemma" / relative_path).resolve()
    base = (paths.lean_engine_dir / "PrisonersDilemma").resolve()

    # Prevent path traversal outside PrisonersDilemma/
    if not str(target).startswith(str(base)):
        return "Error: path escapes the PrisonersDilemma directory"

    if not target.exists():
        return f"Error: file not found: {relative_path}"

    try:
        return target.read_text(encoding="utf-8")
    except OSError as exc:
        return f"Error reading file: {exc}"


def register_lean_tools(handler) -> None:
    """Register the Lean tool implementations into a ToolHandler."""
    handler.register_fn("run_lean_proof", _run_lean_proof)
    handler.register_fn("read_library_file", _read_library_file)

"""Claude tool definitions and implementations for the proof-search and bot-writer agents.

Tools exposed to the proof agent:
  - run_lean_proof: write a candidate proof to a temp file and run lake env lean
  - read_library_file: read any file under engine/PrisonersDilemma/ for few-shot context

Tools exposed to the bot writer agent (in addition to read_library_file):
  - run_lean_build: write a candidate bot file to Bots/LlmGenerations/ and run lake build
"""

from __future__ import annotations

import tempfile
from pathlib import Path
from typing import Any

from pd_runner.config import load_paths
from pd_runner.lean.executor import run_lean_proof_file
from pd_runner.logging_config import get_logger

_log = get_logger("llm.tools")


# ---------------------------------------------------------------------------
# Claude tool schemas (passed to the Anthropic messages API via `tools=`)
# ---------------------------------------------------------------------------

_READ_LIBRARY_FILE_TOOL: dict[str, Any] = {
    "name": "read_library_file",
    "description": (
        "Read a single file under engine/PrisonersDilemma/ (Bots/, Theorems/, or root files). "
        "Use this to fetch existing theorems as few-shot proof examples or to inspect a bot's "
        "definition before writing a proof about it. "
        "IMPORTANT: pass a full file path ending in `.lean`, not a directory — directory listings "
        "are not supported. If you're unsure of the exact filename, the bot definitions you need "
        "are already in your prompt; in general, prefer reasoning from the prompt over guessing "
        "filenames. Files that mention the bots currently under evaluation are intentionally "
        "blocked to prevent answer leakage."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            "relative_path": {
                "type": "string",
                "description": (
                    "Path to a `.lean` file, relative to engine/PrisonersDilemma/. "
                    "Examples: 'Theorems/CooperateBot.lean', 'Bots/DefectBot.lean', "
                    "'Program.lean'. Must end in '.lean' — directories are rejected."
                ),
            }
        },
        "required": ["relative_path"],
    },
}

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
    _READ_LIBRARY_FILE_TOOL,
]


# ---------------------------------------------------------------------------
# Tool implementations
# ---------------------------------------------------------------------------

def _run_lean_proof(lean_source: str, filename_hint: str = "proof_attempt") -> str:
    from pd_runner.services.proof_service import _find_bot_redefinitions

    redefs = _find_bot_redefinitions(lean_source)
    if redefs:
        names = ", ".join(redefs)
        return (
            "exit_code: 1\n"
            "--- stdout ---\n(empty)\n"
            "--- stderr ---\n"
            f"Rejected before compile: your proof file contains `def {names} : Prog` "
            f"declaration(s). Proof files must NOT redefine bots — they cause a namespace "
            f"clash with `PDNew.Bots.{redefs[0]}` at lake build time.\n"
            f"Fix: remove the `def` block(s) and add an import line "
            f"`import PrisonersDilemma.Bots.{redefs[0]}` (and similarly for any other bots). "
            f"Reference the bots by name only."
        )

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

    _log.debug("Running Lean on: %s\n%s", tmp_path.name, lean_source)

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


def _read_library_file(relative_path: str, exclude_bots: frozenset[str] = frozenset()) -> str:
    paths = load_paths()
    target = (paths.lean_engine_dir / "PrisonersDilemma" / relative_path).resolve()
    base = (paths.lean_engine_dir / "PrisonersDilemma").resolve()

    # Prevent path traversal outside PrisonersDilemma/
    if not str(target).startswith(str(base)):
        return "Error: path escapes the PrisonersDilemma directory"

    if not target.exists():
        return f"Error: file not found: {relative_path}"

    if target.is_dir():
        return (
            f"Error: `{relative_path}` is a directory. This tool reads single `.lean` files only — "
            f"directory listings are not supported. Pass a specific filename ending in `.lean`."
        )

    try:
        content = target.read_text(encoding="utf-8")
    except OSError as exc:
        return f"Error reading file: {exc}"

    if exclude_bots:
        # Block only files named after a target bot — i.e. the bot's own definition
        # or its dedicated theorem file. Files that merely mention a target bot in
        # passing (e.g. a comparison theorem in another bot's file) are allowed,
        # since the leak risk lives in files primarily about a target bot.
        stem_lower = target.stem.lower()
        excluded_lower = {b.lower() for b in exclude_bots}
        if stem_lower in excluded_lower:
            return (
                f"Error: access denied — `{relative_path}` is the dedicated file for one of "
                f"the bots under evaluation ({', '.join(sorted(exclude_bots))}). "
                f"To prevent answer leakage during the bot-matrix run, files named after "
                f"the target bots cannot be read via this tool. Reason about the bot "
                f"definitions you were given directly."
            )

    return content


BOT_TOOLS: list[dict[str, Any]] = [
    {
        "name": "run_lean_build",
        "description": (
            "Write a candidate Lean 4 bot definition to a temp file and check it with `lake env lean`. "
            "Returns stdout, stderr, and exit code. "
            "An exit code of 0 with no errors means the bot definition is valid Lean. "
            "Use this tool to iteratively fix syntax and type errors in your bot definition."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "bot_name": {
                    "type": "string",
                    "description": "The name of the bot (e.g. 'KindBot'). Used as the filename and Lean definition name.",
                },
                "lean_source": {
                    "type": "string",
                    "description": (
                        "Complete Lean 4 source for the bot file, including imports, "
                        "namespace declarations, and the bot definition."
                    ),
                },
            },
            "required": ["bot_name", "lean_source"],
        },
    },
    _READ_LIBRARY_FILE_TOOL,
]


def _run_lean_build(bot_name: str, lean_source: str) -> str:
    paths = load_paths()
    lean_dir = paths.lean_engine_dir
    llm_bots_dir = lean_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations"
    llm_bots_dir.mkdir(parents=True, exist_ok=True)

    safe_name = "".join(c if c.isalnum() or c in "_-" else "_" for c in bot_name)
    with tempfile.NamedTemporaryFile(
        mode="w",
        suffix=".lean",
        prefix=f"pd_bot_{safe_name}_",
        dir=llm_bots_dir,
        delete=False,
    ) as f:
        f.write(lean_source)
        bot_file = Path(f.name)

    _log.debug("Writing bot to temp: %s\n%s", bot_file.name, lean_source)

    try:
        result = run_lean_proof_file(lean_dir, bot_file)
    finally:
        bot_file.unlink(missing_ok=True)

    lines = [
        f"exit_code: {result.returncode}",
        "--- stdout ---",
        result.stdout or "(empty)",
        "--- stderr ---",
        result.stderr or "(empty)",
    ]
    return "\n".join(lines)


def register_lean_tools(handler, exclude_bots: frozenset[str] = frozenset()) -> None:
    """Register the Lean tool implementations into a ToolHandler.

    `exclude_bots` is forwarded to `read_library_file` so it refuses to read any
    file whose content references a bot under evaluation (leak prevention).
    """
    handler.register_fn("run_lean_proof", _run_lean_proof)
    handler.register_fn(
        "read_library_file",
        lambda relative_path: _read_library_file(relative_path, exclude_bots=exclude_bots),
    )


def register_bot_tools(handler) -> None:
    """Register the bot-writer tool implementations into a ToolHandler."""
    handler.register_fn("run_lean_build", _run_lean_build)
    handler.register_fn("read_library_file", _read_library_file)

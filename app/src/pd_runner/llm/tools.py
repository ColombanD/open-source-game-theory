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

_ADD_BASE_LEMMA_TOOL: dict[str, Any] = {
    "name": "add_base_lemma",
    "description": (
        "Add a DERIVED rule — a new theorem over the existing proof system `Pf` — to the "
        "persistent lemma library (Theorems/LlmGenerations/LlmLemmas.lean, namespace "
        "`PD.LlmLemmas`). Use this when a proof needs a reusable principle that is a "
        "CONSEQUENCE of existing rules but is not yet stated (the project's history shows "
        "most 'missing rules' are of this kind). The lemma is appended, verified with lake "
        "build, and ROLLED BACK automatically if it fails — so this call is always safe. "
        "Sound by construction: theorems only (`axiom`/`sorry`/`inductive`/`native_decide` "
        "are rejected). Submit BARE declarations — no import/namespace lines; the source "
        "lands inside `namespace PD.LlmLemmas` with `PD` and `PD.BaseTheorems` open. "
        "After an OK response, add `import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas` "
        "to your proof file and use the lemma via `PD.LlmLemmas.<name>`."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            "lemma_name": {
                "type": "string",
                "description": "Short identifier for the lemma block (e.g. 'box_impl_chain').",
            },
            "lean_source": {
                "type": "string",
                "description": (
                    "Bare Lean declaration(s): `theorem`/`lemma` (and `def` for motives), "
                    "fully proved, no imports/namespaces."
                ),
            },
        },
        "required": ["lemma_name", "lean_source"],
    },
}

_PROPOSE_PF_CONSTRUCTOR_TOOL: dict[str, Any] = {
    "name": "propose_pf_constructor",
    "description": (
        "File a proposal for a NEW `Pf` CONSTRUCTOR, for the rare case where a needed "
        "principle is genuinely UNDERIVABLE from the existing rules (you MUST have tried "
        "`add_base_lemma` first and be able to say why derivation fails). This does NOT "
        "modify the engine: it records an evidence bundle for human review. The bundle "
        "requires a SOUNDNESS CERTIFICATE — a complete theorem, which this tool compiles "
        "against the CURRENT engine, proving the rule's interp-level content (what the "
        "conclusion's `Formula.interp` asserts, given the premises' interps; imports "
        "allowed, e.g. `import PrisonersDilemma.BaseTheorems`). A rule whose certificate "
        "does not compile is rejected outright. If the proposal is recorded, finish with "
        "`OUTCOME OPEN — CONSTRUCTOR PROPOSED <name>`."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            "name": {
                "type": "string",
                "description": "Constructor name (e.g. 'iteBranchSearch_f').",
            },
            "constructor_lean": {
                "type": "string",
                "description": (
                    "The constructor declaration exactly as it would appear inside "
                    "`inductive Pf`, including budget side-conditions in the transcript "
                    "cost model (leaves pay their conclusion's size; combining rules pay "
                    "premises + conclusion)."
                ),
            },
            "soundness_certificate_lean": {
                "type": "string",
                "description": (
                    "A COMPLETE Lean file (with imports) proving the rule's interp-level "
                    "content as a theorem over the unchanged engine. No sorry/axiom."
                ),
            },
            "faithfulness_rationale": {
                "type": "string",
                "description": (
                    "Why a PA-like `S` (critch22 Appendix B) genuinely has this capability: "
                    "what finite syntactic activity it transcribes, and why it is not "
                    "semantic completeness / general reflection in disguise."
                ),
            },
            "unblocks": {
                "type": "string",
                "description": "The outcome theorem(s) this rule would make provable, and why.",
            },
            "unblocked_proof_lean": {
                "type": "string",
                "description": (
                    "OPTIONAL but strongly encouraged: a COMPLETE Lean file proving the "
                    "unblocked outcome theorem against the CURRENT engine, with the proposed "
                    "rule stated as an explicit hypothesis (e.g. a theorem parameter "
                    "`(hRule : ∀ k φ, <side-condition> → Pf k <conclusion>)`). The tool "
                    "compiles it and stores it in the bundle — this turns your `unblocks` "
                    "claim into a kernel-checked artifact the integrator can reuse. If it "
                    "fails to compile the proposal is NOT recorded."
                ),
            },
        },
        "required": [
            "name", "constructor_lean", "soundness_certificate_lean",
            "faithfulness_rationale", "unblocks",
        ],
    },
}

# The library-growth tools are only exposed in production mode (empty exclude_bots):
# the eval harness must not mutate the library mid-run, and its leak-free config
# predates the lemma library.
GROWTH_TOOLS: list[dict[str, Any]] = [_ADD_BASE_LEMMA_TOOL, _PROPOSE_PF_CONSTRUCTOR_TOOL]

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
            f"clash with `PD.Bots.{redefs[0]}` at lake build time.\n"
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
    In production mode (empty `exclude_bots`) the library-growth tools are also
    registered: `add_base_lemma` (Tier 1, autonomous — kernel-checked derived rules)
    and `propose_pf_constructor` (Tier 2, human-gated — evidence bundles only).
    """
    handler.register_fn("run_lean_proof", _run_lean_proof)
    handler.register_fn(
        "read_library_file",
        lambda relative_path: _read_library_file(relative_path, exclude_bots=exclude_bots),
    )
    if not exclude_bots:
        from pd_runner.services.constructor_proposals import propose
        from pd_runner.services.lemma_library import add_lemma

        handler.register_fn("add_base_lemma", add_lemma)
        # `propose` accepts keyword args matching the tool schema exactly
        # (unblocked_proof_lean is optional with a default).
        handler.register_fn("propose_pf_constructor", propose)


def register_bot_tools(handler) -> None:
    """Register the bot-writer tool implementations into a ToolHandler."""
    handler.register_fn("run_lean_build", _run_lean_build)
    handler.register_fn("read_library_file", _read_library_file)

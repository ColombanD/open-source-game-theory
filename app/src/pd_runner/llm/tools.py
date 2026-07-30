"""Claude tool definitions and implementations for the proof-search and bot-writer agents.

Tools exposed to the proof agent:
  - run_lean_proof: write a candidate proof to a temp file and run lake env lean
  - read_library_file: read any file under engine/PrisonersDilemma/ for few-shot context

Tools exposed to the bot writer agent (in addition to read_library_file):
  - run_lean_build: write a candidate bot file to Bots/LlmGenerations/ and run lake build
"""

from __future__ import annotations

import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from pd_runner.config import load_paths
from pd_runner.lean.executor import run_lean_proof_file
from pd_runner.logging_config import get_logger
from pd_runner.settings import EvalGuard

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
        "`submit_verdict(verdict=\"constructor_proposed\", proposal_name=<name>, …)`."
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

# The library-growth tools are only exposed when the guard allows growth
# (production mode): the eval harness must not mutate the library mid-run.
GROWTH_TOOLS: list[dict[str, Any]] = [_ADD_BASE_LEMMA_TOOL, _PROPOSE_PF_CONSTRUCTOR_TOOL]


def make_submit_verdict_tool(allow_constructor_proposed: bool) -> dict[str, Any]:
    """The structured-verdict tool schema.

    `constructor_proposed` appears in the enum only when the growth tools are
    registered (a proposal must actually have been filed this run).
    """
    verdicts = ["proved", "open_bistable", "open_blocked"]
    if allow_constructor_proposed:
        verdicts.append("constructor_proposed")
    return {
        "name": "submit_verdict",
        "description": (
            "Submit your FINAL verdict for this matchup. This is the ONLY way to finish — "
            "prose alone does not end the search. For `proved`, include the complete Lean "
            "source: it will be RE-COMPILED and checked against the strict theorem template "
            "(exact theorem name, outcome-equation conclusion, no oracle-conditioning "
            "hypotheses, no census inductions, no library name collisions) before "
            "acceptance; any failure comes back as this tool's result for you to fix. "
            "For `open_bistable` / `open_blocked`, the explanation must cover why ladder "
            "rungs (a) and (b) fail. Calling this tool ends the search only if the verdict "
            "is accepted."
        ),
        "input_schema": {
            "type": "object",
            "properties": {
                "verdict": {"type": "string", "enum": verdicts},
                "lean_source": {
                    "type": "string",
                    "description": (
                        "REQUIRED for `proved`: the complete, compiling theorem file "
                        "(imports, namespace, theorems). Submit EXACTLY the source that "
                        "last passed run_lean_proof."
                    ),
                },
                "left_action": {
                    "type": "string",
                    "enum": ["C", "D", "none"],
                    "description": "REQUIRED for `proved`: the left bot's proven action ('none' for `= none` theorems).",
                },
                "right_action": {
                    "type": "string",
                    "enum": ["C", "D", "none"],
                    "description": "REQUIRED for `proved`: the right bot's proven action ('none' for `= none` theorems).",
                },
                "explanation": {
                    "type": "string",
                    "description": (
                        "REQUIRED. For proved: one sentence on the proof route. For open_*: "
                        "which action pairs are consistent and why rungs (a)/(b) fail; for "
                        "open_blocked, name the wall precisely."
                    ),
                },
                "proposal_name": {
                    "type": "string",
                    "description": (
                        "REQUIRED for `constructor_proposed`: the name of the proposal you "
                        "successfully filed via propose_pf_constructor this session."
                    ),
                },
            },
            "required": ["verdict", "explanation"],
        },
    }


UPDATE_NOTEBOOK_TOOL: dict[str, Any] = {
    "name": "update_notebook",
    "description": (
        "Replace your persistent lab notebook. It is the ONLY free-form memory that "
        "survives into your next attempt if this one fails — distill durable lessons: "
        "what compiled, what failed and WHY, which lemmas/kernels/imports apply, dead "
        "ends to avoid, and your next plan. Replace-whole-text semantics: send the "
        "full notebook every time, longest-lived insights first. Update it whenever "
        "you learn something durable, and always before running out of turns."
    ),
    "input_schema": {
        "type": "object",
        "properties": {
            "notebook": {
                "type": "string",
                "description": "The full replacement notebook text (keep it under 4000 characters).",
            },
        },
        "required": ["notebook"],
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

def compile_proof_source(lean_source: str, filename_hint: str = "proof_attempt"):
    """Write `lean_source` to a temp file inside the engine dir and compile it.

    Returns the raw `LeanExecResult` (returncode/stdout/stderr). Shared by the
    `run_lean_proof` tool and the exit verification's CompileService.
    """
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
        return run_lean_proof_file(lean_dir, tmp_path)
    finally:
        tmp_path.unlink(missing_ok=True)


def _run_lean_proof(
    lean_source: str,
    filename_hint: str = "proof_attempt",
    *,
    exclude_relpath: str | None = None,
    on_attempt=None,
) -> str:
    from pd_runner.services.verdicts import find_bot_redefinitions

    redefs = find_bot_redefinitions(lean_source)
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

    result = compile_proof_source(lean_source, filename_hint)

    if on_attempt is not None:
        on_attempt(lean_source, result)

    lines = [
        f"exit_code: {result.returncode}",
        "--- stdout ---",
        result.stdout or "(empty)",
        "--- stderr ---",
        result.stderr or "(empty)",
    ]

    # Advisory duplicate-name check: the file compiles STANDALONE even when a helper
    # lemma duplicates a library declaration in the same namespace — the clash only
    # surfaces at the umbrella `lake build` when the proof is written to the library,
    # after this agent session is over. Warn NOW so the agent renames in-loop.
    if result.returncode == 0:
        from pd_runner.services.verdicts import (
            find_census_inductions,
            find_library_name_collisions,
        )

        inductions = find_census_inductions(lean_source)
        if inductions:
            lines.append(
                "--- WARNING: hand-rolled Pf induction ---\n"
                f"Your file uses {', '.join(f'`{t}`' for t in inductions)}. Hand-rolled "
                "censuses break with missing-cases on EVERY future constructor addition "
                "and the verdict gate will REFUSE the file. Instantiate the shared "
                "kernels from Base/Exclusion.lean instead (no_provable_tailTo_unreadable / "
                "no_provable_probeFirst_tail / no_provable_searcherPlay_tail / "
                "no_provable_tailToS_floor) — a `refine` plus shape bullets; the census "
                "instances in your few-shots show the pattern."
            )

        collisions = find_library_name_collisions(lean_source, exclude_relpath=exclude_relpath)
        if collisions:
            listing = "\n".join(f"  - `{n}` already declared in {f}" for n, f in collisions)
            lines.append(
                "--- WARNING: library name collisions ---\n"
                f"{listing}\n"
                "The file compiles standalone, but writing it to the library WILL FAIL at "
                "`lake build` (`environment already contains ...`). Rename these "
                "declarations with a matchup-specific prefix (e.g. "
                "`dimcid_obot_<lemma>`) before submitting your verdict."
            )
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
        # Block only files dedicated to a target bot. Files that merely mention a
        # target bot in passing (e.g. a comparison theorem in another bot's file)
        # are allowed, since the leak risk lives in files primarily about a target
        # bot. Dedication is path-based — the single implementation lives in
        # llm/library_layout.py (shared with the few-shot retriever).
        from pd_runner.llm.library_layout import file_bots

        dedicated = file_bots(target, base / "Theorems")
        excluded_lower = {b.lower() for b in exclude_bots}
        if dedicated & excluded_lower:
            return (
                f"Error: access denied — `{relative_path}` is a dedicated file for one of "
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


def register_lean_tools(
    handler,
    exclude_bots: frozenset[str] = frozenset(),
    *,
    guard: EvalGuard | None = None,
    ctx: "RequestContext | None" = None,
    on_attempt=None,
    on_proposal_recorded=None,
) -> None:
    """Register the Lean tool implementations into a ToolHandler.

    `guard.hidden_bots` is forwarded to `read_library_file` so it refuses to
    read any file dedicated to a bot under evaluation (leak prevention).
    When `guard.allow_library_growth` the library-growth tools are also
    registered: `add_base_lemma` (Tier 1, autonomous — kernel-checked derived rules)
    and `propose_pf_constructor` (Tier 2, human-gated — evidence bundles only).

    `ctx` names the matchup so `run_lean_proof`'s collision check can exclude
    the pair's own target module (computed from the request, never from the
    model-supplied filename hint). `on_attempt(lean_source, LeanExecResult)`
    is called for every compile; `on_proposal_recorded(name)` for every
    successfully filed constructor proposal.

    `exclude_bots` is the legacy flag; when `guard` is omitted it is derived
    exactly as the old flag implied (non-empty ⇒ hidden + growth off).
    """
    if guard is None:
        guard = EvalGuard.from_exclude_bots(exclude_bots)
    exclude_relpath = (
        f"Theorems/{ctx.left_bot}/vs_{ctx.right_bot}.lean" if ctx is not None else None
    )
    handler.register_fn(
        "run_lean_proof",
        lambda lean_source, filename_hint="proof_attempt": _run_lean_proof(
            lean_source, filename_hint,
            exclude_relpath=exclude_relpath, on_attempt=on_attempt,
        ),
    )
    handler.register_fn(
        "read_library_file",
        lambda relative_path: _read_library_file(relative_path, exclude_bots=guard.hidden_bots),
    )
    if guard.allow_library_growth:
        from pd_runner.services.constructor_proposals import propose
        from pd_runner.services.lemma_library import add_lemma

        handler.register_fn("add_base_lemma", add_lemma)

        # `propose` accepts keyword args matching the tool schema exactly
        # (unblocked_proof_lean is optional with a default). Successful filings
        # are reported so the verdict gate can cross-check `constructor_proposed`.
        def _propose_and_record(**kwargs):
            result = propose(**kwargs)
            if on_proposal_recorded is not None and str(result).startswith("PROPOSAL RECORDED"):
                raw = kwargs.get("name", "")
                on_proposal_recorded(raw)
                # `propose` sanitizes the name for the bundle dir; accept both forms.
                safe = "".join(c if c.isalnum() or c == "_" else "_" for c in raw)
                if safe != raw:
                    on_proposal_recorded(safe)
            return result

        handler.register_fn("propose_pf_constructor", _propose_and_record)


@dataclass(frozen=True)
class RequestContext:
    """The matchup a proof-agent session is about (drives collision exclusion)."""

    left_bot: str
    right_bot: str


def register_bot_tools(handler) -> None:
    """Register the bot-writer tool implementations into a ToolHandler."""
    handler.register_fn("run_lean_build", _run_lean_build)
    handler.register_fn("read_library_file", _read_library_file)

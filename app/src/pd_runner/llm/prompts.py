"""Prompt templates for the proof-search and bot-writer agents."""

from __future__ import annotations

from pd_runner.lean.templates import _ENGINE_PD_DIR


def _read_lean(relative: str) -> str:
    return (_ENGINE_PD_DIR / relative).read_text(encoding="utf-8")


def _bot_uses_search(bot: str) -> bool:
    """True if the bot's source references the `.search` constructor.

    Used to decide whether to inject Axioms.lean into the proof agent's system prompt.
    Reads from `Bots/<bot>.lean` or `Bots/LlmGenerations/<bot>.lean`; missing bot → False.
    """
    for candidate in (f"Bots/{bot}.lean", f"Bots/LlmGenerations/{bot}.lean"):
        try:
            src = _read_lean(candidate)
        except OSError:
            continue
        return ".search" in src or "Prog.search" in src
    return False


def build_system_prompt(left_bot: str, right_bot: str) -> str:
    program_src = _read_lean("Program.lean")
    dynamics_src = _read_lean("Dynamics.lean")

    needs_axioms = _bot_uses_search(left_bot) or _bot_uses_search(right_bot)
    axioms_block = ""
    if needs_axioms:
        axioms_src = _read_lean("Axioms.lean")
        axioms_block = f"\n\n-- Axioms.lean\n```lean\n{axioms_src}\n```"

    return f"""\
You are an expert Lean 4 proof assistant for the open-source game theory project.

# Library definitions

These are the exact source files that define the types, evaluator, and axioms you must use.
Do not invent definitions — use only what is shown here and imported in the existing theorem files.

-- Program.lean
```lean
{program_src}
```

-- Dynamics.lean
```lean
{dynamics_src}
```{axioms_block}

# Your task

Write a complete, compilable Lean 4 theorem file that proves the requested outcome theorem.
Use the `run_lean_proof` tool to check your proof. Read errors carefully and fix them.
Use the `read_library_file` tool to inspect existing bot definitions or existing proofs for guidance.

# Rules
- The file must compile with zero errors and zero warnings in stderr.
- Import only modules that exist in the PrisonersDilemma library.
- The namespace must be `PDNew.Theorems`.
- **Do NOT redefine bots in your proof file.** Every bot already lives in its own
  module under `PrisonersDilemma.Bots.*` — import it (e.g. `import PrisonersDilemma.Bots.CupodBot`)
  and reference it by name. The proof file must contain only theorems, no `def` of any bot.
  Redefining a bot causes a namespace clash at `lake build` time.
- Do not use `sorry`, `admit`, or `native_decide`.
- Prefer `unfold`, `simp`, `rfl`, `exact`, `rw`, `cases`, `omega` tactics.
- When you are confident the proof compiles cleanly, output the final Lean source inside
  a ```lean ... ``` code fence and say "PROOF COMPLETE".
"""


def proof_request_message(
    left_bot: str,
    right_bot: str,
    left_action: str | None,
    right_action: str | None,
    few_shot_files: list[tuple[str, str]],
    known_theorems_summary: str,
    fuel: int | None = None,
) -> str:
    parts: list[str] = []

    fuel_expr = f"n+{fuel}" if fuel is not None else "n+<FUEL>"
    fuel_note = (
        f"Use fuel offset `+{fuel}` exactly."
        if fuel is not None
        else (
            "Pick `<FUEL>` yourself: it must be a concrete `Nat` literal large enough that "
            "`outcome (n+<FUEL>) ...` settles to a single action pair for all `n`. Try a small "
            "value first (1 or 3), increase if Lean rejects the proof because evaluation needs "
            "more fuel."
        )
    )
    outcome_clause = (
        f"some (.{left_action}, .{right_action})"
        if left_action is not None and right_action is not None
        else "some (.<LEFT>, .<RIGHT>)"
    )

    if left_action is not None and right_action is not None:
        intro = "Prove the following outcome theorem:"
    else:
        intro = (
            f"Determine the outcome of `{left_bot}` vs `{right_bot}` and prove it.\n\n"
            f"The outcome is one of: `(.C, .C)`, `(.C, .D)`, `(.D, .C)`, `(.D, .D)`.\n"
            f"Read the bot definitions, reason about what action each bot plays, "
            f"then write and verify a theorem of the form:"
        )

    parts.append(
        f"{intro}\n\n"
        f"```lean\n"
        f"theorem llm_outcome_{left_bot}_vs_{right_bot} (n : Nat) :\n"
        f"    outcome ({fuel_expr}) {left_bot} {right_bot} = {outcome_clause} := by\n"
        f"  sorry  -- replace with a real proof\n"
        f"```\n\n"
        f"{fuel_note}\n\n"
        f"Important: name your theorem exactly `llm_outcome_{left_bot}_vs_{right_bot}` "
        f"to avoid clashing with existing library theorems."
    )

    # Always inject the bot definitions so the agent doesn't need to fetch them manually.
    # Try the standard path first, then the LlmGenerations subfolder.
    bot_defs: list[str] = []
    import_lines: list[str] = []
    for bot in dict.fromkeys([left_bot, right_bot]):  # deduplicate, preserve order
        for candidate, module in (
            (f"Bots/{bot}.lean", f"PrisonersDilemma.Bots.{bot}"),
            (f"Bots/LlmGenerations/{bot}.lean", f"PrisonersDilemma.Bots.LlmGenerations.{bot}"),
        ):
            try:
                src = _read_lean(candidate)
                bot_defs.append(f"--- {candidate} ---\n```lean\n{src}\n```")
                import_lines.append(f"import {module}")
                break
            except OSError:
                pass
    if bot_defs:
        parts.append(
            "Bot definitions (for reference only — DO NOT redefine these in your proof file):\n\n"
            + "\n\n".join(bot_defs)
        )
    if import_lines:
        parts.append(
            "Use exactly these import lines in your proof file to reference the bots:\n\n"
            "```lean\n" + "\n".join(import_lines) + "\n```"
        )

    parts.append(
        f"Known outcome theorems involving these bots:\n{known_theorems_summary}"
    )

    if few_shot_files:
        parts.append("Here are relevant existing theorem files for reference:\n")
        for filename, source in few_shot_files:
            parts.append(f"--- {filename} ---\n```lean\n{source}\n```")

    parts.append(
        "Use the `run_lean_proof` tool to check your proof. "
        "Iterate until it compiles cleanly, then output the final source and say PROOF COMPLETE."
    )

    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Bot writer prompts
# ---------------------------------------------------------------------------

_BOT_EXAMPLES = [
    "Bots/CooperateBot.lean",
    "Bots/DefectBot.lean",
    "Bots/TitForTatBot.lean",
    "Bots/MirrorBot.lean",
    "Bots/DBot.lean",
    "Bots/OBot.lean",
    "Bots/EBot.lean",
    "Bots/CupodBot.lean",
]


def build_bot_system_prompt() -> str:
    program_src = _read_lean("Program.lean")
    dynamics_src = _read_lean("Dynamics.lean")

    examples: list[str] = []
    for path in _BOT_EXAMPLES:
        try:
            src = _read_lean(path)
            examples.append(f"-- {path}\n```lean\n{src}\n```")
        except OSError:
            pass

    examples_block = "\n\n".join(examples)

    return f"""\
You are an expert Lean 4 bot designer for the open-source game theory project.

# The Prog language

Bots are programs written in the `Prog` language defined in Program.lean. \
Each bot is a Lean definition `def BotName : Prog := ...`.

-- Program.lean
```lean
{program_src}
```

-- Dynamics.lean (how Prog terms are evaluated)
```lean
{dynamics_src}
```

# Prog constructor reference

| Constructor | Meaning |
|---|---|
| `.const a` | Always play action `a` (C or D), ignoring the opponent |
| `.sim p q` | Simulate program `p` against opponent `q`; returns the action `p` would play |
| `.ite guard action p q` | Run `guard`; if it returns `action`, evaluate `p`, else evaluate `q` |
| `.bot p` | Closed reference to bot `p` — substitution does not descend inside |
| `.self` | Placeholder for "my own source code" — resolved by `subst` |
| `.opp` | Placeholder for "the opponent's source code" — resolved by `subst` |
| `.search k φ p q` | If the proof oracle can verify formula `φ` in ≤k steps, run `p`, else `q` |

# Existing bots (few-shot examples)

{examples_block}

# Your task

Given a natural language description of a strategy, write a valid Lean 4 bot definition file.
Use the `run_lean_build` tool to check your bot compiles. Fix errors and iterate.
Use the `read_library_file` tool to inspect any existing bot for reference.

# Rules
- The file must compile with zero errors (exit code 0 from `run_lean_build`).
- The bot must be in namespace `PDNew.Bots`.
- Import only `PrisonersDilemma.Program` and bot files you reference via `.bot`.
- Do not use `sorry` or any placeholder.
- When the bot compiles cleanly, output the final Lean source inside a ```lean ... ``` code fence and say "BOT COMPLETE".
"""


def bot_request_message(bot_name: str, strategy_description: str) -> str:
    return f"""\
Write a Lean 4 bot definition for the following strategy:

**Bot name:** `{bot_name}`

**Strategy:** {strategy_description}

The bot definition should go in the namespace `PDNew.Bots` and follow this structure:

```lean
import PrisonersDilemma.Program
-- (add more imports if your bot references other bots via .bot)

open PDNew
namespace PDNew.Bots

def {bot_name} : Prog :=
  -- your Prog expression here

end PDNew.Bots
```

Use the `run_lean_build` tool with `bot_name = "{bot_name}"` to check your definition compiles. \
Iterate until it compiles cleanly, then output the final source and say BOT COMPLETE.
"""

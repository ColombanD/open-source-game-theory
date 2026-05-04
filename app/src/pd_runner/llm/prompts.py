"""Prompt templates for the proof-search agent."""

from __future__ import annotations

from pd_runner.lean.templates import _ENGINE_PD_DIR

# Bots whose definitions use .search and therefore require Axioms.lean to prove things about them.
_SEARCH_BOTS = {"CupodBot", "DupocBot"}


def _read_lean(relative: str) -> str:
    return (_ENGINE_PD_DIR / relative).read_text(encoding="utf-8")


def build_system_prompt(left_bot: str, right_bot: str) -> str:
    program_src = _read_lean("Program.lean")
    dynamics_src = _read_lean("Dynamics.lean")

    needs_axioms = bool({left_bot, right_bot} & _SEARCH_BOTS)
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
- Do not use `sorry`, `admit`, or `native_decide`.
- Prefer `unfold`, `simp`, `rfl`, `exact`, `rw`, `cases`, `omega` tactics.
- When you are confident the proof compiles cleanly, output the final Lean source inside
  a ```lean ... ``` code fence and say "PROOF COMPLETE".
"""


def proof_request_message(
    left_bot: str,
    right_bot: str,
    left_action: str,
    right_action: str,
    few_shot_files: list[tuple[str, str]],
    known_theorems_summary: str,
) -> str:
    parts: list[str] = []

    parts.append(
        f"Prove the following outcome theorem:\n\n"
        f"```lean\n"
        f"theorem outcome_{left_bot}_vs_{right_bot} (n : Nat) :\n"
        f"    outcome (n+1) {left_bot} {right_bot} = some (.{left_action}, .{right_action}) := by\n"
        f"  sorry  -- replace with a real proof\n"
        f"```"
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

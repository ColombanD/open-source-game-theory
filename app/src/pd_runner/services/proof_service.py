"""M4: Agentic proof-search loop.

Input:  bot pair + claimed outcome
Output: proven Lean source (str) or raises ProofSearchError
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from pd_runner.llm.client import AnthropicClient, ToolHandler
from pd_runner.llm.prompts import build_system_prompt, proof_request_message
from pd_runner.llm.retrieval import list_known_outcome_theorems, retrieve_few_shots
from pd_runner.llm.tools import LEAN_TOOLS, register_lean_tools


@dataclass(frozen=True)
class ProofRequest:
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str
    max_iterations: int = 20
    model: str = "claude-opus-4-7"


@dataclass(frozen=True)
class ProofResult:
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str
    lean_source: str
    iterations_used: int


class ProofSearchError(RuntimeError):
    pass


def search_proof(request: ProofRequest) -> ProofResult:
    """Run the agentic proof-search loop for one theorem.

    Raises ProofSearchError if the agent fails to produce a verified proof.
    """
    few_shots = retrieve_few_shots(request.left_bot, request.right_bot)
    known = list_known_outcome_theorems(request.left_bot, request.right_bot)

    user_message = proof_request_message(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=request.left_action,
        right_action=request.right_action,
        few_shot_files=few_shots,
        known_theorems_summary=known,
    )

    handler = ToolHandler()
    register_lean_tools(handler)

    client = AnthropicClient(
        system_prompt=build_system_prompt(request.left_bot, request.right_bot),
        tools=LEAN_TOOLS,
        model=request.model,
        max_iterations=request.max_iterations,
    )

    # Track how many tool calls were made by monkey-patching the handler.
    iteration_count = [0]
    original_call = handler.call

    def counting_call(tool_name: str, tool_input):
        iteration_count[0] += 1
        return original_call(tool_name, tool_input)

    handler.call = counting_call  # type: ignore[method-assign]

    final_text = client.run(user_message, tool_handler=handler)

    lean_source = _extract_lean_source(final_text)
    if lean_source is None:
        raise ProofSearchError(
            f"Agent did not produce a final Lean source for "
            f"{request.left_bot} vs {request.right_bot}.\n"
            f"Final response:\n{final_text}"
        )

    return ProofResult(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=request.left_action,
        right_action=request.right_action,
        lean_source=lean_source,
        iterations_used=iteration_count[0],
    )


def _extract_lean_source(text: str) -> str | None:
    """Pull the last ```lean ... ``` block from the agent's final response."""
    matches = re.findall(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    if matches:
        return matches[-1].strip()
    return None

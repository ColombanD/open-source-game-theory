"""Bot writer service — generate a Lean 4 bot definition from a NL strategy description."""

from __future__ import annotations

import re
from dataclasses import dataclass

from pd_runner.llm.client import AnthropicClient, ToolHandler
from pd_runner.llm.prompts import build_bot_system_prompt, bot_request_message
from pd_runner.llm.tools import BOT_TOOLS, register_bot_tools
from pd_runner.logging_config import get_logger, TRACE

_log = get_logger("services.bot_service")


@dataclass(frozen=True)
class BotRequest:
    bot_name: str
    strategy_description: str
    max_iterations: int = 20
    model: str = "claude-opus-4-7"


@dataclass(frozen=True)
class BotResult:
    bot_name: str
    lean_source: str
    iterations_used: int


class BotWriteError(RuntimeError):
    pass


def search_bot(request: BotRequest) -> BotResult:
    """Run the agentic bot-writing loop.

    Raises BotWriteError if the agent fails to produce a compiling bot definition.
    """
    system_prompt = build_bot_system_prompt()
    user_message = bot_request_message(request.bot_name, request.strategy_description)

    _log.log(TRACE, "Bot writer system prompt:\n%s", system_prompt)
    _log.log(TRACE, "Bot writer user message:\n%s", user_message)

    handler = ToolHandler()
    register_bot_tools(handler)

    client = AnthropicClient(
        system_prompt=system_prompt,
        tools=BOT_TOOLS,
        model=request.model,
        max_iterations=request.max_iterations,
    )

    iteration_count = [0]
    original_call = handler.call

    def counting_call(tool_name: str, tool_input):
        iteration_count[0] += 1
        return original_call(tool_name, tool_input)

    handler.call = counting_call  # type: ignore[method-assign]

    final_text = client.run(user_message, tool_handler=handler)

    lean_source = _extract_lean_source(final_text)
    if lean_source is None:
        raise BotWriteError(
            f"Agent did not produce a final Lean source for bot '{request.bot_name}'.\n"
            f"Final response:\n{final_text}"
        )

    return BotResult(
        bot_name=request.bot_name,
        lean_source=lean_source,
        iterations_used=iteration_count[0],
    )


def _extract_lean_source(text: str) -> str | None:
    matches = re.findall(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    if matches:
        return matches[-1].strip()
    return None

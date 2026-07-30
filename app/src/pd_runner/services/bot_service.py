"""Bot writer service — generate a Lean 4 bot definition from a NL strategy description."""

from __future__ import annotations

import re
from dataclasses import dataclass

from pd_runner import settings
from pd_runner.llm.client import AnthropicClient, ToolHandler
from pd_runner.llm.prompts import build_bot_system_prompt, bot_request_message
from pd_runner.llm.tools import BOT_TOOLS, register_bot_tools
from pd_runner.logging_config import get_logger, TRACE

_log = get_logger("services.bot_service")


@dataclass(frozen=True)
class BotRequest:
    bot_name: str
    strategy_description: str
    max_iterations: int = settings.DEFAULT_MAX_ITERATIONS
    model: str = settings.DEFAULT_MODEL
    max_tokens: int = settings.DEFAULT_MAX_TOKENS
    thinking_effort: str = settings.DEFAULT_THINKING_EFFORT


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
        max_tokens=request.max_tokens,
        thinking_effort=request.thinking_effort,
    )

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
        iterations_used=client.last_tool_calls,
    )


def _extract_lean_source(text: str) -> str | None:
    matches = re.findall(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    if matches:
        return matches[-1].strip()
    return None

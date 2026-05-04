"""Anthropic SDK-backed LLM client with multi-turn tool use and prompt caching."""

from __future__ import annotations

import anthropic
from typing import Any

_DEFAULT_MODEL = "claude-opus-4-7"
_MAX_TOOL_ITERATIONS = 20


class AnthropicClient:
    """Multi-turn Claude client that drives a tool-use loop.

    Usage:
        client = AnthropicClient(system_prompt="...", tools=[...])
        final_text = client.run(user_message)
    """

    def __init__(
        self,
        system_prompt: str,
        tools: list[dict[str, Any]] | None = None,
        model: str = _DEFAULT_MODEL,
        max_iterations: int = _MAX_TOOL_ITERATIONS,
    ) -> None:
        self._client = anthropic.Anthropic()
        self.model = model
        self.max_iterations = max_iterations
        self.tools = tools or []
        # Cache the system prompt — it is long and stable across iterations.
        self._system: list[dict[str, Any]] = [
            {
                "type": "text",
                "text": system_prompt,
                "cache_control": {"type": "ephemeral"},
            }
        ]

    def run(
        self,
        user_message: str,
        tool_handler: "ToolHandler | None" = None,
    ) -> str:
        """Run a full agentic turn, calling tools until Claude stops or max_iterations hit.

        Args:
            user_message: The initial user message for this turn.
            tool_handler: Object with a ``call(tool_name, tool_input) -> str`` method.
                          Required when ``self.tools`` is non-empty.

        Returns:
            The final assistant text response.
        """
        messages: list[dict[str, Any]] = [{"role": "user", "content": user_message}]

        for _ in range(self.max_iterations):
            kwargs: dict[str, Any] = {
                "model": self.model,
                "max_tokens": 8192,
                "system": self._system,
                "messages": messages,
                "thinking": {"type": "adaptive"},
            }
            if self.tools:
                kwargs["tools"] = self.tools

            response = self._client.messages.create(**kwargs)

            # Append assistant turn (full content block list preserves thinking blocks).
            messages.append({"role": "assistant", "content": response.content})

            if response.stop_reason == "end_turn":
                return _extract_text(response.content)

            if response.stop_reason == "tool_use":
                if tool_handler is None:
                    raise RuntimeError("Claude requested tool use but no tool_handler was provided")

                tool_results: list[dict[str, Any]] = []
                for block in response.content:
                    if block.type == "tool_use":
                        result_text = tool_handler.call(block.name, block.input)
                        tool_results.append(
                            {
                                "type": "tool_result",
                                "tool_use_id": block.id,
                                "content": result_text,
                            }
                        )

                messages.append({"role": "user", "content": tool_results})
                continue

            # Unexpected stop reason — return whatever text exists.
            return _extract_text(response.content)

        raise RuntimeError(
            f"Proof search did not converge within {self.max_iterations} tool-use iterations"
        )


def _extract_text(content: list[Any]) -> str:
    return "\n".join(block.text for block in content if hasattr(block, "text") and block.text)


class ToolHandler:
    """Registry that maps tool names to Python callables.

    Register tools with ``@handler.register("tool_name")`` or
    ``handler.register_fn("tool_name", fn)``.
    """

    def __init__(self) -> None:
        self._registry: dict[str, Any] = {}

    def register(self, name: str):
        def decorator(fn):
            self._registry[name] = fn
            return fn
        return decorator

    def register_fn(self, name: str, fn) -> None:
        self._registry[name] = fn

    def call(self, tool_name: str, tool_input: dict[str, Any]) -> str:
        fn = self._registry.get(tool_name)
        if fn is None:
            return f"Error: unknown tool '{tool_name}'"
        try:
            return str(fn(**tool_input))
        except Exception as exc:
            return f"Error calling tool '{tool_name}': {exc}"

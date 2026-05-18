"""Anthropic SDK-backed LLM client with multi-turn tool use and prompt caching."""

from __future__ import annotations

import time
import anthropic
from typing import Any

from pd_runner.logging_config import get_logger

_log = get_logger("llm.client")

_DEFAULT_MODEL = "claude-opus-4-7"
_MAX_TOOL_ITERATIONS = 20
_RETRY_DELAYS = [5, 15, 30, 60]  # seconds between retries on 529


def _create_with_retry(client: anthropic.Anthropic, kwargs: dict[str, Any]) -> Any:
    for attempt, delay in enumerate(_RETRY_DELAYS, start=1):
        try:
            return client.messages.create(**kwargs)
        except anthropic.APIStatusError as exc:
            if exc.status_code != 529:
                raise
            _log.warning("API overloaded (529), retrying in %ds (attempt %d/%d)...", delay, attempt, len(_RETRY_DELAYS))
            time.sleep(delay)
    return client.messages.create(**kwargs)  # final attempt, let it raise


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
                "max_tokens": 16384,
                "system": self._system,
                "messages": messages,
                "thinking": {"type": "adaptive"},
                "output_config": {"effort": "high"},
            }
            if self.tools:
                kwargs["tools"] = self.tools

            response = _create_with_retry(self._client, kwargs)

            # Append assistant turn (full content block list preserves thinking blocks).
            messages.append({"role": "assistant", "content": response.content})

            assistant_text = _extract_text(response.content)
            if assistant_text:
                _log.debug("Assistant:\n%s", assistant_text)

            if response.stop_reason == "end_turn":
                if not assistant_text:
                    # Empty text but the turn ended — preserve thinking/tool blocks
                    # for post-mortem so the sidecar isn't useless.
                    return _serialize_final_content(response.content, response.stop_reason)
                return assistant_text

            if response.stop_reason == "tool_use":
                if tool_handler is None:
                    raise RuntimeError("Claude requested tool use but no tool_handler was provided")

                tool_results: list[dict[str, Any]] = []
                for block in response.content:
                    if block.type == "tool_use":
                        _log.info("Tool call: %s(%s)", block.name, _fmt_input(block.input))
                        result_text = tool_handler.call(block.name, block.input)
                        _log.debug("Tool result (%s):\n%s", block.name, result_text[:2000] if len(result_text) > 2000 else result_text)
                        tool_results.append(
                            {
                                "type": "tool_result",
                                "tool_use_id": block.id,
                                "content": result_text,
                            }
                        )

                messages.append({"role": "user", "content": tool_results})
                continue

            # Unexpected stop reason — surface a structured dump so callers can
            # see what blocks came back and why the loop exited.
            return _serialize_final_content(response.content, response.stop_reason)

        raise RuntimeError(
            f"Proof search did not converge within {self.max_iterations} tool-use iterations"
        )


def _extract_text(content: list[Any]) -> str:
    return "\n".join(block.text for block in content if hasattr(block, "text") and block.text)


def _serialize_final_content(content: list[Any], stop_reason: str | None) -> str:
    """Human-readable dump of every block in a final assistant turn.

    Used when the turn ends without a text block (e.g. only thinking + tool_use
    or a refusal) so the saved sidecar still tells us what the model did.
    """
    parts: list[str] = [f"[stop_reason={stop_reason}]"]
    for block in content:
        btype = getattr(block, "type", type(block).__name__)
        if btype == "text":
            parts.append(f"--- text ---\n{getattr(block, 'text', '')}")
        elif btype == "thinking":
            thinking = getattr(block, "thinking", "") or getattr(block, "text", "")
            parts.append(f"--- thinking ---\n{thinking}")
        elif btype == "tool_use":
            name = getattr(block, "name", "?")
            tool_input = getattr(block, "input", {})
            parts.append(f"--- tool_use ({name}) ---\n{_fmt_input(tool_input)}")
        else:
            parts.append(f"--- {btype} ---\n{block!r}")
    return "\n".join(parts)


def _fmt_input(tool_input: dict[str, Any]) -> str:
    """Compact one-line summary of tool input for logging."""
    parts = []
    for k, v in tool_input.items():
        s = str(v)
        parts.append(f"{k}={s[:80]!r}" if len(s) > 80 else f"{k}={s!r}")
    return ", ".join(parts)


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

"""Anthropic SDK-backed LLM client with multi-turn tool use and prompt caching."""

from __future__ import annotations

import time
import anthropic
import httpx
from typing import Any

from pd_runner.logging_config import get_logger

_log = get_logger("llm.client")

_DEFAULT_MODEL = "claude-opus-4-7"
_MAX_TOOL_ITERATIONS = 20
_DEFAULT_MAX_TOKENS = 32000
_DEFAULT_THINKING_EFFORT = "medium"

# Explicit thinking budgets per effort level, used on models that accept
# `thinking.type = "enabled"` (budgeted thinking streams deltas progressively
# and bounds thinking length; budgets must stay below max_tokens). Some models
# (claude-opus-4-8) reject "enabled" and only take `{"type": "adaptive"}` +
# `output_config.effort` — the client falls back to that automatically. NOTE
# adaptive thinking on opus-4-8 can go silent for many minutes on hard proof
# turns (bisected 2026-07-27: the same 88k-token request streamed within 2s
# without thinking, stalled indefinitely with adaptive medium) — for such
# models `thinking_effort="none"` (no thinking at all) is the reliable choice.
_THINKING_BUDGETS = {"low": 4096, "medium": 10000, "high": 16384}
_RETRY_DELAYS = [5, 15, 30, 60]  # seconds between retries on 529


# Emit a progress line roughly every this many characters of streamed
# thinking/text. Coarse enough not to flood the SSE log, fine enough that the
# first (long, pre-tool) turn shows it's alive rather than hung.
_STREAM_PROGRESS_EVERY_CHARS = 400


def _stream_once(client: anthropic.Anthropic, kwargs: dict[str, Any]) -> Any:
    """Run a single streamed request, logging coarse progress, and return the
    fully-assembled final message (same object shape as ``messages.create``).

    Streaming is purely for observability: callers get back the identical final
    message (thinking + tool_use + text blocks intact) they would have gotten
    from a blocking ``create``. The deltas are only used to log progress so a
    long pre-tool thinking turn doesn't look like a hang.
    """
    thinking_chars = 0
    text_chars = 0
    next_thinking_mark = _STREAM_PROGRESS_EVERY_CHARS
    next_text_mark = _STREAM_PROGRESS_EVERY_CHARS
    first_token_logged = False
    t0 = time.monotonic()
    last_alive_log = t0

    with client.messages.stream(**kwargs) as stream:
        for event in stream:
            etype = getattr(event, "type", None)
            if etype == "message_start":
                usage = getattr(getattr(event, "message", None), "usage", None)
                _log.info(
                    "message_start after %.1fs (input=%s, cache_read=%s, cache_creation=%s tokens)",
                    time.monotonic() - t0,
                    getattr(usage, "input_tokens", "?"),
                    getattr(usage, "cache_read_input_tokens", "?"),
                    getattr(usage, "cache_creation_input_tokens", "?"),
                )
                continue
            if etype != "content_block_delta":
                # Pings / block boundaries prove the socket is alive even when no
                # content is being generated — surface that, rate-limited.
                now = time.monotonic()
                if now - last_alive_log >= 30:
                    _log.info(
                        "...stream alive (last event: %s), %.0fs elapsed, no new content",
                        etype, now - t0,
                    )
                    last_alive_log = now
                continue
            delta = getattr(event, "delta", None)
            dtype = getattr(delta, "type", None)
            if not first_token_logged:
                _log.info("Model started responding (streaming)...")
                first_token_logged = True
            if dtype == "thinking_delta":
                thinking_chars += len(getattr(delta, "thinking", "") or "")
                if thinking_chars >= next_thinking_mark:
                    _log.info("...thinking (%d chars so far)", thinking_chars)
                    next_thinking_mark = thinking_chars + _STREAM_PROGRESS_EVERY_CHARS
            elif dtype == "text_delta":
                text_chars += len(getattr(delta, "text", "") or "")
                if text_chars >= next_text_mark:
                    _log.info("...writing response (%d chars so far)", text_chars)
                    next_text_mark = text_chars + _STREAM_PROGRESS_EVERY_CHARS
        return stream.get_final_message()


def _create_with_retry(client: anthropic.Anthropic, kwargs: dict[str, Any]) -> Any:
    for attempt, delay in enumerate(_RETRY_DELAYS, start=1):
        try:
            return _stream_once(client, kwargs)
        except anthropic.APIStatusError as exc:
            if exc.status_code != 529:
                raise
            _log.warning("API overloaded (529), retrying in %ds (attempt %d/%d)...", delay, attempt, len(_RETRY_DELAYS))
            time.sleep(delay)
        except anthropic.APIConnectionError as exc:
            # Covers stalled/dropped streams surfaced by the httpx read timeout
            # (APITimeoutError subclasses APIConnectionError). Tool results are
            # only appended after a stream completes, so resending the request
            # never re-executes a tool call.
            _log.warning(
                "Connection error mid-request (%s), retrying in %ds (attempt %d/%d)...",
                type(exc).__name__, delay, attempt, len(_RETRY_DELAYS),
            )
            time.sleep(delay)
    return _stream_once(client, kwargs)  # final attempt, let it raise


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
        max_tokens: int = _DEFAULT_MAX_TOKENS,
        thinking_effort: str = _DEFAULT_THINKING_EFFORT,
    ) -> None:
        # For a STREAMED request the read timeout is per-chunk, not per-turn:
        # deltas arrive every few seconds even mid-thinking, so 300s only trips
        # on a genuinely dead socket (which `timeout=None` would hang on forever).
        # Total turn length stays unbounded.
        self._client = anthropic.Anthropic(
            timeout=httpx.Timeout(connect=30.0, read=300.0, write=30.0, pool=30.0)
        )
        self.model = model
        self.max_iterations = max_iterations
        self.max_tokens = max_tokens
        self.thinking_effort = thinking_effort
        # Flips to True (permanently, per client) when the model rejects
        # budgeted thinking with a 400 telling us to use adaptive instead.
        self._adaptive_only = False
        # The live message list of the most recent run() — kept as a reference
        # so callers can persist the transcript even when run() raises mid-loop.
        self.last_messages: list[dict[str, Any]] = []
        self.tools = tools or []
        # Cache the system prompt — it is long and stable across iterations.
        self._system: list[dict[str, Any]] = [
            {
                "type": "text",
                "text": system_prompt,
                "cache_control": {"type": "ephemeral"},
            }
        ]

    def _thinking_kwargs(self) -> dict[str, Any]:
        """Thinking-related request params for the current effort level and model.

        `"none"` disables thinking entirely — the reliable choice for models where
        adaptive thinking can go silent for minutes (see _THINKING_BUDGETS note).
        """
        if self.thinking_effort == "none":
            return {}
        if self._adaptive_only:
            return {
                "thinking": {"type": "adaptive"},
                "output_config": {"effort": self.thinking_effort},
            }
        return {
            "thinking": {
                "type": "enabled",
                "budget_tokens": _THINKING_BUDGETS.get(
                    self.thinking_effort, _THINKING_BUDGETS["medium"]
                ),
            }
        }

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
        self.last_messages = messages  # same list object — mutations stay visible

        for _ in range(self.max_iterations):
            kwargs: dict[str, Any] = {
                "model": self.model,
                "max_tokens": self.max_tokens,
                "system": self._system,
                "messages": messages,
                **self._thinking_kwargs(),
            }
            if self.tools:
                kwargs["tools"] = self.tools

            try:
                response = _create_with_retry(self._client, kwargs)
            except anthropic.BadRequestError as exc:
                if self._adaptive_only or "thinking.type.enabled" not in str(exc):
                    raise
                # Model only supports adaptive thinking (e.g. claude-opus-4-8).
                # Remember and retry this turn with the adaptive config.
                self._adaptive_only = True
                _log.warning(
                    "Model %s rejects budgeted thinking; falling back to adaptive "
                    "(effort=%s). Adaptive can stall for minutes on hard turns — "
                    "consider thinking_effort='none' for this model.",
                    self.model, self.thinking_effort,
                )
                kwargs.pop("thinking", None)
                kwargs.pop("output_config", None)
                kwargs.update(self._thinking_kwargs())
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


def serialize_messages(messages: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """JSON-safe copy of a run's message list, SDK content blocks included.

    Assistant turns hold pydantic block objects (text/thinking/tool_use); user
    turns hold plain strings or tool_result dicts. Everything is flattened to
    plain JSON so the full transcript can be persisted alongside an attempt.
    """
    out: list[dict[str, Any]] = []
    for m in messages:
        content = m["content"]
        if isinstance(content, str):
            out.append({"role": m["role"], "content": content})
            continue
        blocks: list[Any] = []
        for b in content:
            if hasattr(b, "model_dump"):
                blocks.append(b.model_dump(mode="json", exclude_none=True))
            else:
                blocks.append(b)
        out.append({"role": m["role"], "content": blocks})
    return out


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

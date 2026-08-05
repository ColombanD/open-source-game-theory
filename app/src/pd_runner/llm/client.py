"""Anthropic SDK-backed LLM client with multi-turn tool use and prompt caching."""

from __future__ import annotations

import time
import anthropic
import httpx
from dataclasses import dataclass
from typing import Any

from pd_runner.logging_config import get_logger
from pd_runner.settings import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_MAX_TOKENS,
    DEFAULT_MODEL,
    DEFAULT_THINKING_EFFORT,
    RetryPolicy,
    cost_usd,
)

_log = get_logger("llm.client")

_DEFAULT_MODEL = DEFAULT_MODEL
_MAX_TOOL_ITERATIONS = DEFAULT_MAX_ITERATIONS
_DEFAULT_MAX_TOKENS = DEFAULT_MAX_TOKENS
_DEFAULT_THINKING_EFFORT = DEFAULT_THINKING_EFFORT


@dataclass
class UsageTotals:
    """Accumulated API usage across the turns of one run/episode."""

    input_tokens: int = 0
    output_tokens: int = 0
    cache_read_tokens: int = 0
    cache_creation_tokens: int = 0

    def add_message_usage(self, usage: Any) -> None:
        self.input_tokens += getattr(usage, "input_tokens", 0) or 0
        self.output_tokens += getattr(usage, "output_tokens", 0) or 0
        self.cache_read_tokens += getattr(usage, "cache_read_input_tokens", 0) or 0
        self.cache_creation_tokens += getattr(usage, "cache_creation_input_tokens", 0) or 0

    def merge(self, other: "UsageTotals") -> None:
        self.input_tokens += other.input_tokens
        self.output_tokens += other.output_tokens
        self.cache_read_tokens += other.cache_read_tokens
        self.cache_creation_tokens += other.cache_creation_tokens

    @property
    def total_input_tokens(self) -> int:
        """All prompt tokens the model read, cached or not."""
        return self.input_tokens + self.cache_read_tokens + self.cache_creation_tokens

    def cache_hit_rate(self) -> float:
        total = self.total_input_tokens
        return (self.cache_read_tokens / total) if total else 0.0

    def cost_usd(self, model: str) -> float | None:
        return cost_usd(
            model,
            input_tokens=self.input_tokens,
            output_tokens=self.output_tokens,
            cache_read_tokens=self.cache_read_tokens,
            cache_creation_tokens=self.cache_creation_tokens,
        )

    def as_dict(self) -> dict[str, int]:
        return {
            "input_tokens": self.input_tokens,
            "output_tokens": self.output_tokens,
            "cache_read_tokens": self.cache_read_tokens,
            "cache_creation_tokens": self.cache_creation_tokens,
        }


@dataclass(frozen=True)
class EpisodeStop:
    """Sentinel a stop-tool handler returns to end the episode immediately.

    `payload` carries the accepted tool input (the verdict); `confirmation_text`
    is appended as the tool_result so the transcript stays well-formed. A stop
    with `payload=None` ends the episode without a verdict (`end_reason` names
    why, e.g. "verification_cap").
    """

    payload: dict[str, Any] | None
    confirmation_text: str = "Verdict accepted. The search is complete."
    end_reason: str = "verdict"


@dataclass
class EpisodeResult:
    """What one episode produced, verdict or not."""

    verdict_input: dict[str, Any] | None
    end_reason: str  # "verdict" | "turn_cap" | "context_guard" | "end_turn" | "unexpected_stop" | custom EpisodeStop reasons
    turns_used: int
    tool_calls_used: int
    usage: UsageTotals
    final_text: str
    messages: list[dict[str, Any]]

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


def _is_budgeted_thinking_rejection(exc: anthropic.BadRequestError) -> bool:
    """True when the model rejects `thinking.type = "enabled"` (budgeted) and
    only accepts adaptive thinking (e.g. claude-opus-4-8).

    Inspects the structured error body first; falls back to the string form.
    """
    try:
        body = exc.body
        if isinstance(body, dict):
            message = body.get("error", {}).get("message", "")
            if message:
                return "thinking.type.enabled" in message
    except AttributeError:
        pass
    return "thinking.type.enabled" in str(exc)


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


def _retry_after_seconds(exc: anthropic.APIStatusError) -> float | None:
    """The server's `retry-after` header in seconds, if present and sane."""
    try:
        value = exc.response.headers.get("retry-after")
        if value is None:
            return None
        seconds = float(value)
        return seconds if 0 < seconds <= 300 else None
    except (AttributeError, TypeError, ValueError):
        return None


def _create_with_retry(
    client: anthropic.Anthropic,
    kwargs: dict[str, Any],
    policy: RetryPolicy = RetryPolicy(),
) -> Any:
    """Run one streamed request with retries on transient failures.

    len(policy.delays_s)+1 total attempts; the LAST attempt re-raises the
    caught exception (no unguarded extra call). Retries are safe: tool results
    are only appended after a stream completes, so resending the request never
    re-executes a tool call.
    """
    attempts = len(policy.delays_s) + 1
    for attempt in range(1, attempts + 1):
        try:
            return _stream_once(client, kwargs)
        except anthropic.APIStatusError as exc:
            if exc.status_code not in policy.retry_statuses or attempt == attempts:
                raise
            delay = policy.delays_s[attempt - 1]
            if policy.honor_retry_after:
                server_delay = _retry_after_seconds(exc)
                if server_delay is not None:
                    delay = max(delay, server_delay)
            _log.warning(
                "API error %d, retrying in %.0fs (attempt %d/%d)...",
                exc.status_code, delay, attempt, attempts,
            )
            time.sleep(delay)
        except anthropic.APIConnectionError as exc:
            # Covers stalled/dropped streams surfaced by the httpx read timeout
            # (APITimeoutError subclasses APIConnectionError).
            if attempt == attempts:
                raise
            delay = policy.delays_s[attempt - 1]
            _log.warning(
                "Connection error mid-request (%s), retrying in %.0fs (attempt %d/%d)...",
                type(exc).__name__, delay, attempt, attempts,
            )
            time.sleep(delay)
    raise AssertionError("unreachable")  # loop always returns or raises


class AnthropicClient:
    """Multi-turn Claude client that drives a tool-use loop.

    Usage:
        client = AnthropicClient(system_prompt="...", tools=[...])
        final_text = client.run(user_message)
    """

    def __init__(
        self,
        system_prompt: str | list[str],
        tools: list[dict[str, Any]] | None = None,
        model: str = _DEFAULT_MODEL,
        max_iterations: int = _MAX_TOOL_ITERATIONS,
        max_tokens: int = _DEFAULT_MAX_TOKENS,
        thinking_effort: str = _DEFAULT_THINKING_EFFORT,
    ) -> None:
        # For a STREAMED request the read timeout is per-chunk, not per-turn:
        # deltas arrive every few seconds even mid-thinking, so 300s only trips
        # on a genuinely dead socket (which `timeout=None` would hang on forever).
        # Total turn length stays unbounded. max_retries=0: retry scheduling is
        # ours (_create_with_retry) — the SDK's built-in retries must not stack.
        self._client = anthropic.Anthropic(
            timeout=httpx.Timeout(connect=30.0, read=300.0, write=30.0, pool=30.0),
            max_retries=0,
        )
        self.retry_policy = RetryPolicy()
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
        # First-class counters for the most recent run() — live objects updated
        # per turn, so they are meaningful even when run() raises mid-loop.
        self.last_usage: UsageTotals = UsageTotals()
        self.last_turns: int = 0
        self.last_tool_calls: int = 0
        # Cache breakpoint on the tools array (its last entry): tool definitions
        # are fixed for the whole run and render before the system blocks.
        self.tools = [dict(t) for t in (tools or [])]
        if self.tools:
            self.tools[-1] = {**self.tools[-1], "cache_control": {"type": "ephemeral"}}
        # Cache the system prompt — long and stable across iterations. A list of
        # blocks gets one breakpoint EACH (block A pair-invariant, block B
        # pair/session content), so a matrix run re-reads block A from cache
        # across different matchups.
        blocks = [system_prompt] if isinstance(system_prompt, str) else list(system_prompt)
        self._system: list[dict[str, Any]] = [
            {"type": "text", "text": text, "cache_control": {"type": "ephemeral"}}
            for text in blocks
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
        self.last_usage = UsageTotals()
        self.last_turns = 0
        self.last_tool_calls = 0

        for _ in range(self.max_iterations):
            _set_moving_cache_marker(messages)
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
                response = _create_with_retry(self._client, kwargs, self.retry_policy)
            except anthropic.BadRequestError as exc:
                if self._adaptive_only or not _is_budgeted_thinking_rejection(exc):
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
                response = _create_with_retry(self._client, kwargs, self.retry_policy)

            self.last_turns += 1
            self.last_usage.add_message_usage(getattr(response, "usage", None))

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
                        self.last_tool_calls += 1
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

    def run_episode(
        self,
        user_content: str | list[dict[str, Any]],
        tool_handler: "ToolHandler",
        *,
        max_turns: int,
        stop_tool: str | None = None,
        context_token_guard: int = 350_000,
        notebook_tool: str | None = None,
    ) -> EpisodeResult:
        """Run one bounded episode of the tool loop.

        Differences from `run()`:
          - ends gracefully (never raises) on turn cap or context growth — the
            caller decides whether to start a fresh episode;
          - `stop_tool`: when that tool's handler returns an `EpisodeStop`, the
            confirmation tool_result is appended and the episode returns with
            the accepted payload — no extra API call;
          - a model that ends its turn without calling the stop tool gets ONE
            reminder user-turn per occurrence (bounded by `max_turns`);
          - `notebook_tool`: when the episode ends WITHOUT a verdict and that
            tool was not called within the last 2 turns, ONE forced reflection
            turn runs so the memory survives into the next episode;
          - first-class per-episode counters and usage totals in the result.
        """
        messages: list[dict[str, Any]] = [{"role": "user", "content": user_content}]
        self.last_messages = messages  # same list object — mutations stay visible
        usage = UsageTotals()
        self.last_usage = usage
        turns = 0
        tool_calls = 0
        final_text = ""
        last_notebook_turn = 0

        def call_model() -> Any:
            _set_moving_cache_marker(messages)
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
                return _create_with_retry(self._client, kwargs, self.retry_policy)
            except anthropic.BadRequestError as exc:
                if self._adaptive_only or not _is_budgeted_thinking_rejection(exc):
                    raise
                self._adaptive_only = True
                _log.warning(
                    "Model %s rejects budgeted thinking; falling back to adaptive "
                    "(effort=%s).", self.model, self.thinking_effort,
                )
                kwargs.pop("thinking", None)
                kwargs.pop("output_config", None)
                kwargs.update(self._thinking_kwargs())
                return _create_with_retry(self._client, kwargs, self.retry_policy)

        def reflect_if_stale() -> None:
            """The hybrid notebook trigger's enforced half: one reflection turn
            before the context is discarded, unless the notebook is fresh."""
            nonlocal turns, tool_calls
            if notebook_tool is None:
                return
            # Fresh enough: updated within the last 2 turns (0 = never updated).
            if last_notebook_turn > 0 and (turns - last_notebook_turn) <= 2:
                return
            messages.append({
                "role": "user",
                "content": (
                    "This attempt is over and your context is about to be DISCARDED. "
                    f"Save your durable lessons NOW with a single `{notebook_tool}` call: "
                    "what compiled, what failed and WHY, dead ends to avoid, and the plan "
                    "for the next attempt."
                ),
            })
            try:
                response = call_model()
            except Exception as exc:  # reflection is best-effort — never sink the episode
                _log.warning("Forced reflection turn failed (%s); continuing without it", exc)
                messages.pop()
                return
            turns += 1
            self.last_turns = turns
            usage.add_message_usage(getattr(response, "usage", None))
            messages.append({"role": "assistant", "content": response.content})
            if response.stop_reason == "tool_use":
                tool_results = []
                for block in response.content:
                    if block.type != "tool_use":
                        continue
                    tool_calls += 1
                    self.last_tool_calls = tool_calls
                    outcome = tool_handler.call(block.name, block.input)
                    tool_results.append({
                        "type": "tool_result",
                        "tool_use_id": block.id,
                        "content": outcome.confirmation_text
                        if isinstance(outcome, EpisodeStop) else str(outcome),
                    })
                messages.append({"role": "user", "content": tool_results})

        def result(end_reason: str, verdict: dict[str, Any] | None = None) -> EpisodeResult:
            if verdict is None and end_reason != "unexpected_stop":
                reflect_if_stale()
            return EpisodeResult(
                verdict_input=verdict,
                end_reason=end_reason,
                turns_used=turns,
                tool_calls_used=tool_calls,
                usage=usage,
                final_text=final_text,
                messages=messages,
            )

        while turns < max_turns:
            response = call_model()

            turns += 1
            self.last_turns = turns
            response_usage = getattr(response, "usage", None)
            usage.add_message_usage(response_usage)

            messages.append({"role": "assistant", "content": response.content})
            assistant_text = _extract_text(response.content)
            if assistant_text:
                final_text = assistant_text
                _log.debug("Assistant:\n%s", assistant_text)

            # Context guard: the prompt this response just paid is the floor for
            # the next one — end the episode before it overflows.
            prompt_tokens = sum(
                getattr(response_usage, f, 0) or 0
                for f in ("input_tokens", "cache_read_input_tokens", "cache_creation_input_tokens")
            )
            over_guard = prompt_tokens > context_token_guard

            if response.stop_reason == "tool_use":
                stop: EpisodeStop | None = None
                tool_results: list[dict[str, Any]] = []
                for block in response.content:
                    if block.type != "tool_use":
                        continue
                    tool_calls += 1
                    self.last_tool_calls = tool_calls
                    if stop is not None:
                        # A stop was already accepted this turn; answer the
                        # remaining tool_use blocks so the transcript stays
                        # well-formed, but do not execute them.
                        tool_results.append({
                            "type": "tool_result",
                            "tool_use_id": block.id,
                            "content": "(not executed — the episode ended on an accepted verdict)",
                        })
                        continue
                    _log.info("Tool call: %s(%s)", block.name, _fmt_input(block.input))
                    if notebook_tool is not None and block.name == notebook_tool:
                        last_notebook_turn = turns
                    outcome = tool_handler.call(block.name, block.input)
                    if isinstance(outcome, EpisodeStop) and block.name == stop_tool:
                        stop = outcome
                        tool_results.append({
                            "type": "tool_result",
                            "tool_use_id": block.id,
                            "content": outcome.confirmation_text,
                        })
                        continue
                    result_text = str(outcome)
                    _log.debug(
                        "Tool result (%s):\n%s", block.name,
                        result_text[:2000] if len(result_text) > 2000 else result_text,
                    )
                    tool_results.append({
                        "type": "tool_result",
                        "tool_use_id": block.id,
                        "content": result_text,
                    })
                messages.append({"role": "user", "content": tool_results})
                if stop is not None:
                    return result(stop.end_reason, verdict=stop.payload)
                if over_guard:
                    _log.warning(
                        "Context guard: prompt reached %d tokens (> %d) — ending episode",
                        prompt_tokens, context_token_guard,
                    )
                    return result("context_guard")
                continue

            if response.stop_reason == "end_turn":
                if stop_tool is None:
                    return result("end_turn")
                if over_guard or turns >= max_turns:
                    return result("context_guard" if over_guard else "turn_cap")
                # The model stopped talking without submitting a verdict —
                # remind it once and let it continue (still bounded by max_turns).
                _log.info("Model ended turn without calling %s — sending reminder", stop_tool)
                messages.append({
                    "role": "user",
                    "content": (
                        f"You have not submitted a verdict. Call the `{stop_tool}` tool "
                        "with your final verdict to finish — your text response alone "
                        "does not end the search."
                    ),
                })
                continue

            # Unexpected stop reason (refusal, max_tokens, …)
            final_text = _serialize_final_content(response.content, response.stop_reason)
            return result("unexpected_stop")

        return result("turn_cap")


def _set_moving_cache_marker(messages: list[dict[str, Any]]) -> None:
    """Keep exactly one conversation cache breakpoint, on the newest user turn.

    On turn 1 this caches the (large, static) user prefix; on turn N it caches
    the whole conversation so only the newest content is re-read at full price.
    Older markers are stripped so the total breakpoint count stays within the
    API's limit of 4 (tools + up to 2 system blocks + this one). Assistant
    turns hold SDK pydantic blocks and are left untouched.
    """
    for message in messages:
        content = message.get("content")
        if isinstance(content, list):
            for block in content:
                if isinstance(block, dict):
                    block.pop("cache_control", None)
    last = messages[-1]
    if last.get("role") != "user":
        return
    content = last["content"]
    if isinstance(content, str):
        last["content"] = [
            {"type": "text", "text": content, "cache_control": {"type": "ephemeral"}}
        ]
    elif isinstance(content, list) and content and isinstance(content[-1], dict):
        content[-1]["cache_control"] = {"type": "ephemeral"}


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
        content = m.get("content")
        if content is None or isinstance(content, str):
            # Plain-dict message (OpenAI-compat transcripts carry extra keys
            # like tool_calls / tool_call_id / _reasoning) — already JSON-safe.
            out.append(dict(m))
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

    def call(self, tool_name: str, tool_input: dict[str, Any]) -> "str | EpisodeStop":
        fn = self._registry.get(tool_name)
        if fn is None:
            return f"Error: unknown tool '{tool_name}'"
        try:
            outcome = fn(**tool_input)
        except Exception as exc:
            return f"Error calling tool '{tool_name}': {exc}"
        if isinstance(outcome, EpisodeStop):
            return outcome
        return str(outcome)

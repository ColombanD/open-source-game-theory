"""OpenAI-compatible chat-completions client with the same tool-loop interface
as `AnthropicClient` — for non-Anthropic models (Leanstral 1.5 via Mistral's
hosted endpoint, or anything served by vLLM).

Deliberately a SEPARATE class rather than a shared base: the Anthropic path is
the calibrated thesis baseline (prompt-cache breakpoints, budgeted/adaptive
thinking, streaming observability) and must stay byte-stable, while this path
normalizes a different wire format (tool_calls with JSON-string arguments,
role="tool" results, no cache control). The episode-loop SEMANTICS — stop-tool
verdicts, the missing-verdict reminder, the context guard, the forced notebook
reflection — are mirrored 1:1 from `client.py`; change them in both places.

Messages are kept as plain JSON-able dicts (they double as request payload and
persisted transcript). Keys starting with "_" (e.g. "_reasoning") are
transcript-only and stripped before sending.
"""

from __future__ import annotations

import json
import time
from typing import Any

import httpx
import openai

from pd_runner.logging_config import get_logger
from pd_runner.llm.client import (
    EpisodeResult,
    EpisodeStop,
    ToolHandler,
    UsageTotals,
    _fmt_input,
)
from pd_runner.settings import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_MAX_TOKENS,
    DEFAULT_THINKING_EFFORT,
    ProviderSpec,
    RetryPolicy,
)

_log = get_logger("llm.openai_client")


def _to_openai_tools(tools: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Anthropic tool schema ({name, description, input_schema}) → OpenAI
    function-calling schema. `cache_control` keys are dropped."""
    out = []
    for t in tools:
        out.append({
            "type": "function",
            "function": {
                "name": t["name"],
                "description": t.get("description", ""),
                "parameters": t.get("input_schema", {"type": "object", "properties": {}}),
            },
        })
    return out


def _wire_messages(messages: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Strip transcript-only keys (leading underscore) before sending."""
    wire = []
    for m in messages:
        wire.append({k: v for k, v in m.items() if not k.startswith("_")})
    return wire


def _retry_after_seconds(exc: openai.APIStatusError) -> float | None:
    try:
        value = exc.response.headers.get("retry-after")
        if value is None:
            return None
        seconds = float(value)
        return seconds if 0 < seconds <= 300 else None
    except (AttributeError, TypeError, ValueError):
        return None


class OpenAICompatClient:
    """Multi-turn tool-loop client for OpenAI-compatible endpoints.

    Public interface matches `AnthropicClient`: same constructor kwargs, same
    `run()` / `run_episode()` signatures and result types, same live
    `last_messages` / `last_usage` / `last_turns` / `last_tool_calls`.
    """

    def __init__(
        self,
        system_prompt: str | list[str],
        tools: list[dict[str, Any]] | None = None,
        model: str = "",
        max_iterations: int = DEFAULT_MAX_ITERATIONS,
        max_tokens: int = DEFAULT_MAX_TOKENS,
        thinking_effort: str = DEFAULT_THINKING_EFFORT,
        *,
        provider: ProviderSpec,
        api_key: str | None = None,
    ) -> None:
        self._client = openai.OpenAI(
            base_url=provider.base_url,
            # vLLM ignores the key but the SDK requires a non-empty string.
            api_key=api_key or "EMPTY",
            timeout=httpx.Timeout(connect=30.0, read=600.0, write=30.0, pool=30.0),
            max_retries=0,
        )
        self.retry_policy = RetryPolicy()
        self.model = model
        self._wire_model = provider.model_id or model
        self._reasoning_efforts = provider.reasoning_efforts
        self.max_iterations = max_iterations
        self.max_tokens = max_tokens
        self.thinking_effort = thinking_effort
        # Flips to True (permanently, per client) when the endpoint rejects the
        # reasoning_effort parameter.
        self._no_reasoning_param = False
        self.last_messages: list[dict[str, Any]] = []
        self.last_usage: UsageTotals = UsageTotals()
        self.last_turns: int = 0
        self.last_tool_calls: int = 0
        self.tools = _to_openai_tools(tools or [])
        blocks = [system_prompt] if isinstance(system_prompt, str) else list(system_prompt)
        self._system_text = "\n\n".join(blocks)

    # -- request layer ------------------------------------------------------

    def _request_kwargs(self, messages: list[dict[str, Any]]) -> dict[str, Any]:
        kwargs: dict[str, Any] = {
            "model": self._wire_model,
            "max_tokens": self.max_tokens,
            "messages": [{"role": "system", "content": self._system_text}]
            + _wire_messages(messages),
        }
        if self.tools:
            kwargs["tools"] = self.tools
        effort = self._mapped_effort()
        if effort is not None and not self._no_reasoning_param:
            # Leanstral/vLLM reasoning dial; dropped on a runtime rejection.
            kwargs["extra_body"] = {"reasoning_effort": effort}
        return kwargs

    def _mapped_effort(self) -> str | None:
        """thinking_effort mapped onto the provider's supported reasoning
        values; None = omit the parameter. With a declared supported set,
        "none" is sent EXPLICITLY (the endpoint may default reasoning on),
        and any thinking request maps to the nearest supported level."""
        effort = self.thinking_effort
        allowed = self._reasoning_efforts
        if allowed is None:
            return None if effort == "none" else effort
        if effort in allowed:
            return effort
        if effort != "none" and "high" in allowed:
            return "high"
        return None

    def _create_with_retry(self, kwargs: dict[str, Any]) -> Any:
        policy = self.retry_policy
        attempts = len(policy.delays_s) + 1
        for attempt in range(1, attempts + 1):
            t0 = time.monotonic()
            try:
                response = self._client.chat.completions.create(**kwargs)
                _log.info(
                    "Completion in %.1fs (prompt=%s, completion=%s tokens)",
                    time.monotonic() - t0,
                    getattr(response.usage, "prompt_tokens", "?"),
                    getattr(response.usage, "completion_tokens", "?"),
                )
                return response
            except openai.BadRequestError as exc:
                if (
                    self._no_reasoning_param
                    or "extra_body" not in kwargs
                    or "reasoning" not in str(exc).lower()
                ):
                    raise
                # Endpoint rejects the reasoning dial — retry once without it.
                self._no_reasoning_param = True
                _log.warning(
                    "Model %s rejects reasoning_effort; continuing without it",
                    self.model,
                )
                kwargs = {k: v for k, v in kwargs.items() if k != "extra_body"}
                return self._create_with_retry(kwargs)
            except openai.APIStatusError as exc:
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
            except openai.APIConnectionError as exc:
                if attempt == attempts:
                    raise
                delay = policy.delays_s[attempt - 1]
                _log.warning(
                    "Connection error (%s), retrying in %.0fs (attempt %d/%d)...",
                    type(exc).__name__, delay, attempt, attempts,
                )
                time.sleep(delay)
        raise AssertionError("unreachable")

    # -- response normalization --------------------------------------------

    @staticmethod
    def _add_usage(totals: UsageTotals, usage: Any) -> int:
        """Fold one response's usage into `totals`; returns total prompt tokens
        (the context-guard measure). Cached prompt tokens, when reported, are
        counted as cache reads."""
        prompt = getattr(usage, "prompt_tokens", 0) or 0
        completion = getattr(usage, "completion_tokens", 0) or 0
        details = getattr(usage, "prompt_tokens_details", None)
        cached = getattr(details, "cached_tokens", 0) or 0
        totals.input_tokens += max(prompt - cached, 0)
        totals.cache_read_tokens += cached
        totals.output_tokens += completion
        return prompt

    @staticmethod
    def _split_content(content: Any) -> tuple[str, str]:
        """Normalize message content to (text, reasoning).

        Mistral's reasoning models return a LIST of typed blocks
        ([{type: "thinking", thinking: [{type: "text", text: ...}]},
          {type: "text", text: ...}]) instead of a plain string.
        """
        if content is None:
            return "", ""
        if isinstance(content, str):
            return content, ""
        text_parts: list[str] = []
        thinking_parts: list[str] = []
        for block in content:
            if not isinstance(block, dict):
                block = {"type": getattr(block, "type", None),
                         "text": getattr(block, "text", None),
                         "thinking": getattr(block, "thinking", None)}
            btype = block.get("type")
            if btype == "text":
                text_parts.append(block.get("text") or "")
            elif btype == "thinking":
                inner = block.get("thinking")
                if isinstance(inner, str):
                    thinking_parts.append(inner)
                elif isinstance(inner, list):
                    thinking_parts.extend(
                        (b.get("text") if isinstance(b, dict) else getattr(b, "text", None)) or ""
                        for b in inner
                    )
        return "\n".join(p for p in text_parts if p), "\n".join(p for p in thinking_parts if p)

    @classmethod
    def _assistant_dict(cls, message: Any) -> dict[str, Any]:
        """SDK message → plain JSON-able assistant dict (transcript + payload)."""
        text, thinking = cls._split_content(message.content)
        entry: dict[str, Any] = {
            "role": "assistant",
            "content": text,
        }
        if thinking:
            entry["_reasoning"] = thinking
        if message.tool_calls:
            entry["tool_calls"] = [
                {
                    "id": tc.id,
                    "type": "function",
                    "function": {
                        "name": tc.function.name,
                        "arguments": tc.function.arguments,
                    },
                }
                for tc in message.tool_calls
            ]
        # vLLM reasoning parsers expose reasoning_content; keep it in the
        # transcript but never send it back.
        reasoning = getattr(message, "reasoning_content", None)
        if reasoning and "_reasoning" not in entry:
            entry["_reasoning"] = reasoning
        return entry

    @staticmethod
    def _parse_arguments(raw: str) -> dict[str, Any] | None:
        try:
            parsed = json.loads(raw or "{}")
        except json.JSONDecodeError:
            return None
        return parsed if isinstance(parsed, dict) else None

    def _execute_tool_calls(
        self,
        entry: dict[str, Any],
        tool_handler: ToolHandler,
        *,
        stop_tool: str | None = None,
        on_notebook: Any = None,
    ) -> tuple[list[dict[str, Any]], EpisodeStop | None]:
        """Run every tool call in an assistant turn; returns the role="tool"
        result messages and the accepted EpisodeStop, if any. Calls after an
        accepted stop are answered but not executed (transcript stays valid)."""
        results: list[dict[str, Any]] = []
        stop: EpisodeStop | None = None
        for tc in entry.get("tool_calls", []):
            call_id = tc["id"]
            name = tc["function"]["name"]
            self.last_tool_calls += 1
            if stop is not None:
                results.append({
                    "role": "tool",
                    "tool_call_id": call_id,
                    "content": "(not executed — the episode ended on an accepted verdict)",
                })
                continue
            tool_input = self._parse_arguments(tc["function"]["arguments"])
            if tool_input is None:
                results.append({
                    "role": "tool",
                    "tool_call_id": call_id,
                    "content": f"Error: arguments for '{name}' were not valid JSON. "
                    "Re-issue the call with a well-formed JSON object.",
                })
                continue
            _log.info("Tool call: %s(%s)", name, _fmt_input(tool_input))
            if on_notebook is not None and name == on_notebook[0]:
                on_notebook[1]()
            outcome = tool_handler.call(name, tool_input)
            if isinstance(outcome, EpisodeStop) and name == stop_tool:
                stop = outcome
                results.append({
                    "role": "tool",
                    "tool_call_id": call_id,
                    "content": outcome.confirmation_text,
                })
                continue
            text = outcome.confirmation_text if isinstance(outcome, EpisodeStop) else str(outcome)
            _log.debug("Tool result (%s):\n%s", name, text[:2000])
            results.append({"role": "tool", "tool_call_id": call_id, "content": text})
        return results, stop

    # -- public interface ---------------------------------------------------

    def run(
        self,
        user_message: str,
        tool_handler: "ToolHandler | None" = None,
    ) -> str:
        """Full agentic turn: call tools until the model stops or max_iterations."""
        messages: list[dict[str, Any]] = [{"role": "user", "content": user_message}]
        self.last_messages = messages
        self.last_usage = UsageTotals()
        self.last_turns = 0
        self.last_tool_calls = 0

        for _ in range(self.max_iterations):
            response = self._create_with_retry(self._request_kwargs(messages))
            self.last_turns += 1
            self._add_usage(self.last_usage, getattr(response, "usage", None))

            choice = response.choices[0]
            entry = self._assistant_dict(choice.message)
            messages.append(entry)
            if entry["content"]:
                _log.debug("Assistant:\n%s", entry["content"])

            if entry.get("tool_calls"):
                if tool_handler is None:
                    raise RuntimeError("Model requested tool use but no tool_handler was provided")
                results, _ = self._execute_tool_calls(entry, tool_handler)
                messages.extend(results)
                continue

            if choice.finish_reason == "length":
                return f"[finish_reason=length]\n{entry['content']}"
            return entry["content"]

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
        """One bounded episode of the tool loop — semantics mirror
        `AnthropicClient.run_episode` (see that docstring)."""
        if not isinstance(user_content, str):
            user_content = "\n".join(
                b.get("text", "") for b in user_content if isinstance(b, dict)
            )
        messages: list[dict[str, Any]] = [{"role": "user", "content": user_content}]
        self.last_messages = messages
        usage = UsageTotals()
        self.last_usage = usage
        turns = 0
        self.last_tool_calls = 0
        final_text = ""
        last_notebook_turn = 0

        def note_notebook() -> None:
            nonlocal last_notebook_turn
            last_notebook_turn = turns

        def call_model() -> Any:
            return self._create_with_retry(self._request_kwargs(messages))

        def reflect_if_stale() -> None:
            nonlocal turns
            if notebook_tool is None:
                return
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
            self._add_usage(usage, getattr(response, "usage", None))
            entry = self._assistant_dict(response.choices[0].message)
            messages.append(entry)
            if entry.get("tool_calls"):
                results, _ = self._execute_tool_calls(
                    entry, tool_handler, on_notebook=(notebook_tool, note_notebook),
                )
                messages.extend(results)

        def result(end_reason: str, verdict: dict[str, Any] | None = None) -> EpisodeResult:
            if verdict is None and end_reason != "unexpected_stop":
                reflect_if_stale()
            return EpisodeResult(
                verdict_input=verdict,
                end_reason=end_reason,
                turns_used=turns,
                tool_calls_used=self.last_tool_calls,
                usage=usage,
                final_text=final_text,
                messages=messages,
            )

        while turns < max_turns:
            response = call_model()
            turns += 1
            self.last_turns = turns
            prompt_tokens = self._add_usage(usage, getattr(response, "usage", None))
            over_guard = prompt_tokens > context_token_guard

            choice = response.choices[0]
            entry = self._assistant_dict(choice.message)
            messages.append(entry)
            if entry["content"]:
                final_text = entry["content"]
                _log.debug("Assistant:\n%s", entry["content"])

            if entry.get("tool_calls"):
                results, stop = self._execute_tool_calls(
                    entry, tool_handler,
                    stop_tool=stop_tool,
                    on_notebook=(notebook_tool, note_notebook) if notebook_tool else None,
                )
                messages.extend(results)
                if stop is not None:
                    return result(stop.end_reason, verdict=stop.payload)
                if over_guard:
                    _log.warning(
                        "Context guard: prompt reached %d tokens (> %d) — ending episode",
                        prompt_tokens, context_token_guard,
                    )
                    return result("context_guard")
                continue

            if choice.finish_reason in ("stop", None):
                if stop_tool is None:
                    return result("end_turn")
                if over_guard or turns >= max_turns:
                    return result("context_guard" if over_guard else "turn_cap")
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

            # length cutoff, content filter, …
            final_text = f"[finish_reason={choice.finish_reason}]\n{entry['content']}"
            return result("unexpected_stop")

        return result("turn_cap")

"""Unit tests for llm/client.py hardening: retry policy, usage accounting,
and the contained adaptive-thinking fallback detection."""

from __future__ import annotations

import httpx
import pytest

import anthropic

from pd_runner.llm import client as client_mod
from pd_runner.llm.client import UsageTotals, _create_with_retry, _is_budgeted_thinking_rejection
from pd_runner.settings import RetryPolicy


def _status_error(status_code: int, message: str = "err", headers: dict | None = None):
    request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
    response = httpx.Response(status_code, request=request, headers=headers or {})
    return anthropic.APIStatusError(message, response=response, body={"error": {"message": message}})


def _bad_request(message: str):
    request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
    response = httpx.Response(400, request=request)
    return anthropic.BadRequestError(message, response=response, body={"error": {"message": message}})


# ---------------------------------------------------------------------------
# _create_with_retry
# ---------------------------------------------------------------------------


def _patch_stream(monkeypatch, outcomes):
    """Make _stream_once pop from `outcomes`: exceptions raise, values return."""
    calls = []

    def fake_stream_once(client, kwargs):
        calls.append(kwargs)
        outcome = outcomes.pop(0)
        if isinstance(outcome, Exception):
            raise outcome
        return outcome

    monkeypatch.setattr(client_mod, "_stream_once", fake_stream_once)
    monkeypatch.setattr(client_mod.time, "sleep", lambda s: None)
    return calls


def test_retry_recovers_from_transient_statuses(monkeypatch):
    for status in (429, 500, 529):
        calls = _patch_stream(monkeypatch, [_status_error(status), "ok"])
        assert _create_with_retry(None, {}, RetryPolicy()) == "ok"
        assert len(calls) == 2


def test_no_retry_on_non_retryable_status(monkeypatch):
    calls = _patch_stream(monkeypatch, [_status_error(400)])
    with pytest.raises(anthropic.APIStatusError):
        _create_with_retry(None, {}, RetryPolicy())
    assert len(calls) == 1


def test_retry_exhaustion_reraises_without_extra_attempt(monkeypatch):
    policy = RetryPolicy(delays_s=(0.0, 0.0))
    # 3 attempts total (2 delays + 1); the 4th outcome must never be consumed.
    outcomes = [_status_error(529), _status_error(529), _status_error(529), "never"]
    calls = _patch_stream(monkeypatch, outcomes)
    with pytest.raises(anthropic.APIStatusError):
        _create_with_retry(None, {}, policy)
    assert len(calls) == 3
    assert outcomes == ["never"]


def test_retry_honors_retry_after_header(monkeypatch):
    sleeps: list[float] = []
    calls = _patch_stream(monkeypatch, [_status_error(429, headers={"retry-after": "42"}), "ok"])
    monkeypatch.setattr(client_mod.time, "sleep", lambda s: sleeps.append(s))
    assert _create_with_retry(None, {}, RetryPolicy()) == "ok"
    assert sleeps == [42.0]
    assert len(calls) == 2


def test_retry_on_connection_error(monkeypatch):
    request = httpx.Request("POST", "https://api.anthropic.com/v1/messages")
    calls = _patch_stream(
        monkeypatch, [anthropic.APIConnectionError(request=request), "ok"]
    )
    assert _create_with_retry(None, {}, RetryPolicy()) == "ok"
    assert len(calls) == 2


# ---------------------------------------------------------------------------
# _is_budgeted_thinking_rejection
# ---------------------------------------------------------------------------


def test_thinking_rejection_detected_from_body():
    exc = _bad_request("thinking.type.enabled is not supported on this model; use adaptive")
    assert _is_budgeted_thinking_rejection(exc) is True


def test_thinking_rejection_not_confused_with_other_400s():
    exc = _bad_request("max_tokens is too large for this model")
    assert _is_budgeted_thinking_rejection(exc) is False


# ---------------------------------------------------------------------------
# UsageTotals
# ---------------------------------------------------------------------------


class _FakeUsage:
    input_tokens = 100
    output_tokens = 50
    cache_read_input_tokens = 900
    cache_creation_input_tokens = 0


def test_usage_totals_accumulation_and_cache_hit_rate():
    totals = UsageTotals()
    totals.add_message_usage(_FakeUsage())
    totals.add_message_usage(_FakeUsage())
    assert totals.input_tokens == 200
    assert totals.output_tokens == 100
    assert totals.cache_read_tokens == 1800
    assert totals.cache_hit_rate() == pytest.approx(1800 / 2000)
    assert totals.cost_usd("claude-opus-4-7") == pytest.approx(
        (200 * 5.0 + 1800 * 0.5 + 100 * 25.0) / 1_000_000
    )


def test_usage_totals_handles_missing_usage():
    totals = UsageTotals()
    totals.add_message_usage(None)
    assert totals.total_input_tokens == 0
    assert totals.cache_hit_rate() == 0.0
    assert totals.cost_usd("unknown-model") is None


# ---------------------------------------------------------------------------
# run_episode (fake transport)
# ---------------------------------------------------------------------------

from types import SimpleNamespace

from pd_runner.llm.client import AnthropicClient, EpisodeStop, ToolHandler


def _text_block(text):
    return SimpleNamespace(type="text", text=text)


def _tool_block(name, tool_input, block_id="tu_1"):
    return SimpleNamespace(type="tool_use", name=name, input=tool_input, id=block_id)


def _response(blocks, stop_reason, prompt_tokens=1000):
    usage = SimpleNamespace(
        input_tokens=prompt_tokens, output_tokens=10,
        cache_read_input_tokens=0, cache_creation_input_tokens=0,
    )
    return SimpleNamespace(content=blocks, stop_reason=stop_reason, usage=usage)


def _episode_client(monkeypatch, responses):
    client = AnthropicClient(system_prompt="sys", tools=[{"name": "t"}])
    seq = list(responses)
    monkeypatch.setattr(
        client_mod, "_create_with_retry", lambda c, kwargs, policy=None: seq.pop(0)
    )
    return client


def test_run_episode_accepts_verdict(monkeypatch):
    client = _episode_client(monkeypatch, [
        _response([_tool_block("submit_verdict", {"verdict": "proved"})], "tool_use"),
    ])
    handler = ToolHandler()
    handler.register_fn("submit_verdict", lambda **kw: EpisodeStop(payload=kw))

    result = client.run_episode("go", handler, max_turns=5, stop_tool="submit_verdict")
    assert result.end_reason == "verdict"
    assert result.verdict_input == {"verdict": "proved"}
    assert result.turns_used == 1
    assert result.tool_calls_used == 1
    # Confirmation tool_result was appended for the stop call.
    assert result.messages[-1]["content"][0]["type"] == "tool_result"


def test_run_episode_rejected_verdict_continues(monkeypatch):
    client = _episode_client(monkeypatch, [
        _response([_tool_block("submit_verdict", {"verdict": "proved"})], "tool_use"),
        _response([_tool_block("submit_verdict", {"verdict": "proved", "ok": True})], "tool_use"),
    ])
    calls = []

    def verdict(**kw):
        calls.append(kw)
        if len(calls) == 1:
            return "Verdict rejected: fix it"
        return EpisodeStop(payload=kw)

    handler = ToolHandler()
    handler.register_fn("submit_verdict", verdict)

    result = client.run_episode("go", handler, max_turns=5, stop_tool="submit_verdict")
    assert result.end_reason == "verdict"
    assert result.turns_used == 2
    assert len(calls) == 2


def test_run_episode_reminds_on_bare_end_turn(monkeypatch):
    client = _episode_client(monkeypatch, [
        _response([_text_block("done I think")], "end_turn"),
        _response([_tool_block("submit_verdict", {"verdict": "open_bistable"})], "tool_use"),
    ])
    handler = ToolHandler()
    handler.register_fn("submit_verdict", lambda **kw: EpisodeStop(payload=kw))

    result = client.run_episode("go", handler, max_turns=5, stop_tool="submit_verdict")
    assert result.end_reason == "verdict"
    assert result.turns_used == 2
    # A reminder user-turn was inserted between the two model turns. (The moving
    # cache marker may have converted its string content to block form.)
    reminder = result.messages[2]
    content = reminder["content"]
    text = content if isinstance(content, str) else content[0]["text"]
    assert reminder["role"] == "user" and "submit_verdict" in text


def test_run_episode_turn_cap_triggers_forced_reflection(monkeypatch):
    notebook_calls = []
    client = _episode_client(monkeypatch, [
        _response([_tool_block("run_lean_proof", {"lean_source": "x"})], "tool_use"),
        _response([_tool_block("run_lean_proof", {"lean_source": "y"})], "tool_use"),
        # the forced reflection turn:
        _response([_tool_block("update_notebook", {"notebook": "lessons"})], "tool_use"),
    ])
    handler = ToolHandler()
    handler.register_fn("run_lean_proof", lambda **kw: "exit_code: 1")
    handler.register_fn(
        "update_notebook", lambda notebook: notebook_calls.append(notebook) or "ok"
    )

    result = client.run_episode(
        "go", handler, max_turns=2, stop_tool="submit_verdict",
        notebook_tool="update_notebook",
    )
    assert result.end_reason == "turn_cap"
    assert notebook_calls == ["lessons"]
    assert result.turns_used == 3  # 2 regular + 1 reflection


def test_run_episode_context_guard_ends_gracefully(monkeypatch):
    client = _episode_client(monkeypatch, [
        _response([_tool_block("run_lean_proof", {"lean_source": "x"})], "tool_use",
                   prompt_tokens=400_000),
    ])
    handler = ToolHandler()
    handler.register_fn("run_lean_proof", lambda **kw: "exit_code: 1")

    result = client.run_episode(
        "go", handler, max_turns=5, stop_tool="submit_verdict",
        context_token_guard=350_000,
    )
    assert result.end_reason == "context_guard"
    assert result.turns_used == 1


def test_moving_cache_marker_single_breakpoint():
    from pd_runner.llm.client import _set_moving_cache_marker

    messages = [
        {"role": "user", "content": "big static prefix"},
        {"role": "assistant", "content": [SimpleNamespace(type="text", text="hi")]},
        {"role": "user", "content": [{"type": "tool_result", "tool_use_id": "1", "content": "ok"}]},
    ]
    _set_moving_cache_marker(messages)
    # marker only on the newest user turn's last block
    assert messages[-1]["content"][-1]["cache_control"] == {"type": "ephemeral"}
    # a later call moves it and strips the old one
    messages.append({"role": "user", "content": [{"type": "tool_result", "tool_use_id": "2", "content": "ok2"}]})
    _set_moving_cache_marker(messages)
    assert "cache_control" not in messages[2]["content"][-1]
    assert messages[-1]["content"][-1]["cache_control"] == {"type": "ephemeral"}


def test_client_marks_tools_and_system_blocks():
    client = AnthropicClient(system_prompt=["block A", "block B"],
                             tools=[{"name": "a"}, {"name": "b"}])
    assert "cache_control" not in client.tools[0]
    assert client.tools[1]["cache_control"] == {"type": "ephemeral"}
    assert [b["text"] for b in client._system] == ["block A", "block B"]
    assert all(b["cache_control"] == {"type": "ephemeral"} for b in client._system)

"""Tests for the OpenAI-compatible client and the provider factory."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from pd_runner.llm.client import AnthropicClient, EpisodeStop, ToolHandler, serialize_messages
from pd_runner.llm.factory import make_llm_client
from pd_runner.llm.openai_client import OpenAICompatClient, _to_openai_tools
from pd_runner.settings import ProviderSpec


# ---------------------------------------------------------------------------
# Fakes
# ---------------------------------------------------------------------------

def _response(content=None, tool_calls=None, finish_reason="stop",
              prompt_tokens=100, completion_tokens=10):
    message = SimpleNamespace(
        content=content,
        tool_calls=[
            SimpleNamespace(
                id=tc["id"],
                function=SimpleNamespace(name=tc["name"], arguments=tc["arguments"]),
            )
            for tc in (tool_calls or [])
        ] or None,
        reasoning_content=None,
    )
    return SimpleNamespace(
        choices=[SimpleNamespace(message=message, finish_reason=finish_reason)],
        usage=SimpleNamespace(
            prompt_tokens=prompt_tokens,
            completion_tokens=completion_tokens,
            prompt_tokens_details=None,
        ),
    )


class _FakeTransport:
    """Stands in for openai.OpenAI: returns scripted responses, records requests."""

    def __init__(self, responses):
        self._responses = list(responses)
        self.requests = []
        self.chat = SimpleNamespace(completions=SimpleNamespace(create=self._create))

    def _create(self, **kwargs):
        self.requests.append(kwargs)
        return self._responses.pop(0)


def _make_client(responses, **kwargs) -> tuple[OpenAICompatClient, _FakeTransport]:
    client = OpenAICompatClient(
        system_prompt=["block A", "block B"],
        tools=[{"name": "t", "description": "d", "input_schema": {"type": "object"}}],
        model="leanstral-1-5",
        provider=ProviderSpec("http://localhost:1", "X", key_optional=True),
        **kwargs,
    )
    transport = _FakeTransport(responses)
    client._client = transport
    return client, transport


# ---------------------------------------------------------------------------
# Schema conversion
# ---------------------------------------------------------------------------

def test_tool_schema_conversion():
    converted = _to_openai_tools([
        {"name": "t", "description": "d", "input_schema": {"type": "object"},
         "cache_control": {"type": "ephemeral"}},
    ])
    assert converted == [{
        "type": "function",
        "function": {"name": "t", "description": "d", "parameters": {"type": "object"}},
    }]


# ---------------------------------------------------------------------------
# run(): tool loop
# ---------------------------------------------------------------------------

def test_run_executes_tools_then_returns_text():
    client, transport = _make_client([
        _response(tool_calls=[{"id": "c1", "name": "t", "arguments": '{"x": 1}'}],
                  finish_reason="tool_calls"),
        _response(content="done", finish_reason="stop"),
    ])
    seen = []
    handler = ToolHandler()
    handler.register_fn("t", lambda x: seen.append(x) or "tool-ok")

    assert client.run("go", tool_handler=handler) == "done"
    assert seen == [1]
    # The tool result went back as a role="tool" message tied to the call id.
    tool_msgs = [m for m in client.last_messages if m.get("role") == "tool"]
    assert tool_msgs == [{"role": "tool", "tool_call_id": "c1", "content": "tool-ok"}]
    # System prompt is the first wire message on every request.
    assert transport.requests[0]["messages"][0] == {
        "role": "system", "content": "block A\n\nblock B",
    }
    assert client.last_usage.total_input_tokens == 200
    assert client.last_usage.output_tokens == 20


def test_run_invalid_json_arguments_bounce_back():
    client, _ = _make_client([
        _response(tool_calls=[{"id": "c1", "name": "t", "arguments": "not json"}],
                  finish_reason="tool_calls"),
        _response(content="recovered"),
    ])
    handler = ToolHandler()
    handler.register_fn("t", lambda **k: "never reached")

    assert client.run("go", tool_handler=handler) == "recovered"
    tool_msg = next(m for m in client.last_messages if m.get("role") == "tool")
    assert "not valid JSON" in tool_msg["content"]


# ---------------------------------------------------------------------------
# run_episode(): verdict stop, reminder, serialization
# ---------------------------------------------------------------------------

def _verdict_handler(payload):
    handler = ToolHandler()
    handler.register_fn(
        "submit_verdict", lambda **k: EpisodeStop(payload=k, end_reason="verdict")
    )
    return handler


def test_episode_ends_on_stop_tool():
    client, _ = _make_client([
        _response(tool_calls=[{
            "id": "c1", "name": "submit_verdict",
            "arguments": '{"verdict": "proved"}',
        }], finish_reason="tool_calls"),
    ])
    result = client.run_episode(
        "go", _verdict_handler({}), max_turns=5, stop_tool="submit_verdict",
    )
    assert result.end_reason == "verdict"
    assert result.verdict_input == {"verdict": "proved"}
    assert result.turns_used == 1
    # Transcript is JSON-serializable as persisted by _persist_episode.
    assert serialize_messages(result.messages)


def test_episode_reminds_on_missing_verdict():
    client, transport = _make_client([
        _response(content="I think it's proved.", finish_reason="stop"),
        _response(tool_calls=[{
            "id": "c1", "name": "submit_verdict", "arguments": '{"verdict": "proved"}',
        }], finish_reason="tool_calls"),
    ])
    result = client.run_episode(
        "go", _verdict_handler({}), max_turns=5, stop_tool="submit_verdict",
    )
    assert result.end_reason == "verdict"
    reminder = transport.requests[1]["messages"][-1]
    assert reminder["role"] == "user" and "submit_verdict" in reminder["content"]


def test_episode_turn_cap_reflects_to_notebook():
    client, transport = _make_client([
        _response(content="thinking...", finish_reason="stop"),
        # the forced reflection turn:
        _response(tool_calls=[{
            "id": "c9", "name": "update_notebook", "arguments": '{"text": "lessons"}',
        }], finish_reason="tool_calls"),
    ])
    notes = []
    handler = ToolHandler()
    handler.register_fn("update_notebook", lambda text: notes.append(text) or "ok")

    result = client.run_episode(
        "go", handler, max_turns=2, stop_tool=None, notebook_tool="update_notebook",
    )
    assert result.end_reason == "end_turn"
    assert notes == ["lessons"]
    assert "DISCARDED" in transport.requests[-1]["messages"][-1]["content"]


# ---------------------------------------------------------------------------
# Provider quirks: block-list content, reasoning-effort mapping
# ---------------------------------------------------------------------------

def test_block_list_content_normalized():
    """Mistral reasoning models return content as typed blocks, not a string."""
    client, _ = _make_client([_response()])
    entry = client._assistant_dict(SimpleNamespace(
        content=[
            {"type": "thinking", "thinking": [{"type": "text", "text": "hmm"}], "closed": True},
            {"type": "text", "text": "the answer"},
        ],
        tool_calls=None,
        reasoning_content=None,
    ))
    assert entry["content"] == "the answer"
    assert entry["_reasoning"] == "hmm"
    # Transcript-only keys never go back on the wire.
    from pd_runner.llm.openai_client import _wire_messages
    assert "_reasoning" not in _wire_messages([entry])[0]


def test_reasoning_effort_mapped_to_supported_values():
    spec = ProviderSpec("http://x", "K", key_optional=True,
                        reasoning_efforts=("none", "high"))
    for requested, expected in [
        ("none", "none"),      # explicit off — endpoint may default reasoning on
        ("low", "high"),
        ("medium", "high"),
        ("high", "high"),
    ]:
        client = OpenAICompatClient(
            system_prompt="s", model="m", provider=spec, thinking_effort=requested,
        )
        assert client._mapped_effort() == expected

    # No declared set: pass through, omitting only "none".
    open_spec = ProviderSpec("http://x", "K", key_optional=True)
    client = OpenAICompatClient(
        system_prompt="s", model="m", provider=open_spec, thinking_effort="medium",
    )
    assert client._mapped_effort() == "medium"
    client = OpenAICompatClient(
        system_prompt="s", model="m", provider=open_spec, thinking_effort="none",
    )
    assert client._mapped_effort() is None


def test_wire_model_id_override():
    spec = ProviderSpec("http://x", "K", key_optional=True, model_id="labs-m")
    client = OpenAICompatClient(system_prompt="s", model="m", provider=spec)
    assert client._request_kwargs([])["model"] == "labs-m"
    assert client.model == "m"  # app-level name unchanged (eval records, prices)


# ---------------------------------------------------------------------------
# Factory routing
# ---------------------------------------------------------------------------

def test_factory_routes_claude_to_anthropic(monkeypatch):
    monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    client = make_llm_client(system_prompt="s", model="claude-opus-4-7")
    assert isinstance(client, AnthropicClient)


def test_factory_routes_leanstral_to_openai_compat(monkeypatch):
    monkeypatch.delenv("PD_OPENAI_BASE_URL", raising=False)
    monkeypatch.setenv("MISTRAL_API_KEY", "k")
    client = make_llm_client(system_prompt="s", model="leanstral-1-5")
    assert isinstance(client, OpenAICompatClient)


def test_factory_requires_api_key(monkeypatch):
    monkeypatch.delenv("PD_OPENAI_BASE_URL", raising=False)
    monkeypatch.delenv("MISTRAL_API_KEY", raising=False)
    with pytest.raises(ValueError, match="MISTRAL_API_KEY"):
        make_llm_client(system_prompt="s", model="leanstral-1-5")


def test_factory_rejects_unknown_model(monkeypatch):
    monkeypatch.delenv("PD_OPENAI_BASE_URL", raising=False)
    with pytest.raises(ValueError, match="No provider known"):
        make_llm_client(system_prompt="s", model="mystery-model")


def test_factory_base_url_override_serves_any_model(monkeypatch):
    monkeypatch.setenv("PD_OPENAI_BASE_URL", "http://localhost:8000/v1")
    monkeypatch.delenv("PD_OPENAI_API_KEY", raising=False)
    client = make_llm_client(system_prompt="s", model="mystery-model")
    assert isinstance(client, OpenAICompatClient)

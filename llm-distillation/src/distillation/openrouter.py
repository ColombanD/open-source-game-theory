"""Thin wrapper over the OpenAI SDK pointed at OpenRouter.

OpenRouter speaks the OpenAI chat-completions API, so we reuse the official SDK
with a custom ``base_url``. The model reasons freely and ends with a
``My action <<A>>`` marker, which we parse into a C/D action.
"""

from __future__ import annotations

import re

from openai import OpenAI

OPENROUTER_BASE_URL = "https://openrouter.ai/api/v1"

# Matches the required final marker, e.g. "My action <<C>>" (case-insensitive,
# tolerant of surrounding whitespace).
_ACTION_RE = re.compile(r"My action\s*<<\s*([CD])\s*>>", re.IGNORECASE)


def make_client(api_key: str) -> OpenAI:
    """Create an OpenAI SDK client configured for OpenRouter."""
    return OpenAI(base_url=OPENROUTER_BASE_URL, api_key=api_key)


def parse_action(text: str) -> str | None:
    """Extract the action from the model's ``My action <<A>>`` marker.

    Returns ``"C"``, ``"D"``, or ``None`` if no well-formed marker is present.
    If the marker appears more than once, the last occurrence wins (the model's
    final answer, not a mention inside its reasoning).
    """
    matches = _ACTION_RE.findall(text)
    if not matches:
        return None
    return matches[-1].upper()


def query_action(
    client: OpenAI, model: str, prompt: str, temperature: float,
    reasoning_effort: str | None = None,
) -> tuple[str | None, str]:
    """Query the model once and return ``(parsed_action, raw_text)``.

    ``parsed_action`` is ``"C"``, ``"D"``, or ``None`` if the reply has no
    well-formed ``My action <<A>>`` marker. ``raw_text`` keeps the full reply
    (including the model's reasoning).

    ``reasoning_effort`` (e.g. ``"high"``) is passed through OpenRouter's unified
    ``reasoning`` parameter. When ``None`` it is omitted entirely, so models that
    do not support reasoning are unaffected.
    """
    extra_body = (
        {"reasoning": {"effort": reasoning_effort}} if reasoning_effort else {}
    )
    response = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=temperature,
        extra_body=extra_body,
    )
    raw = response.choices[0].message.content or ""
    return parse_action(raw), raw

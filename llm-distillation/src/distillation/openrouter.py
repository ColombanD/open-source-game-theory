"""Thin wrapper over the OpenAI SDK pointed at OpenRouter.

OpenRouter speaks the OpenAI chat-completions API, so we reuse the official SDK
with a custom ``base_url``. The model is queried for a single C/D action.
"""

from __future__ import annotations

from openai import OpenAI

OPENROUTER_BASE_URL = "https://openrouter.ai/api/v1"


def make_client(api_key: str) -> OpenAI:
    """Create an OpenAI SDK client configured for OpenRouter."""
    return OpenAI(base_url=OPENROUTER_BASE_URL, api_key=api_key)


def parse_action(text: str) -> str | None:
    """Extract a single action from a model reply: ``"C"``, ``"D"``, or None.

    The reply is expected to be just the action, but we tolerate surrounding
    whitespace/punctuation. If both or neither appear, we cannot decide.
    """
    upper = text.upper()
    has_c, has_d = "C" in upper, "D" in upper
    if has_c == has_d:  # both present or both absent -> ambiguous
        return None
    return "C" if has_c else "D"


def query_action(
    client: OpenAI, model: str, prompt: str, temperature: float
) -> tuple[str | None, str]:
    """Query the model once and return ``(parsed_action, raw_text)``.

    ``parsed_action`` is ``"C"``, ``"D"``, or ``None`` if the reply is ambiguous.
    """
    response = client.chat.completions.create(
        model=model,
        messages=[{"role": "user", "content": prompt}],
        temperature=temperature,
    )
    raw = response.choices[0].message.content or ""
    return parse_action(raw), raw

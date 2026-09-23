"""Provider-agnostic client construction.

`make_llm_client` keeps every agent (proof loop, bot writer, integration)
model-swappable from the existing `--model` flags: `claude-*` models keep the
calibrated `AnthropicClient` path untouched; anything else resolves through
`settings.OPENAI_COMPAT_PROVIDERS` (or the PD_OPENAI_BASE_URL override for a
self-hosted vLLM) to an `OpenAICompatClient` with the same interface.
"""

from __future__ import annotations

import os
from typing import Any

from pd_runner.llm.client import AnthropicClient
from pd_runner.settings import (
    DEFAULT_MAX_ITERATIONS,
    DEFAULT_MAX_TOKENS,
    DEFAULT_MODEL,
    DEFAULT_THINKING_EFFORT,
    resolve_provider,
)

LlmClient = Any  # AnthropicClient | OpenAICompatClient — identical interfaces


def make_llm_client(
    system_prompt: str | list[str],
    tools: list[dict[str, Any]] | None = None,
    model: str = DEFAULT_MODEL,
    max_iterations: int = DEFAULT_MAX_ITERATIONS,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    thinking_effort: str = DEFAULT_THINKING_EFFORT,
) -> LlmClient:
    if model.startswith("claude"):
        return AnthropicClient(
            system_prompt=system_prompt,
            tools=tools,
            model=model,
            max_iterations=max_iterations,
            max_tokens=max_tokens,
            thinking_effort=thinking_effort,
        )

    provider = resolve_provider(model)
    if provider is None:
        raise ValueError(
            f"No provider known for model '{model}'. Either add it to "
            "settings.OPENAI_COMPAT_PROVIDERS or set PD_OPENAI_BASE_URL "
            "(and PD_OPENAI_API_KEY if needed) for a self-hosted endpoint."
        )
    api_key = os.getenv(provider.api_key_env)
    if not api_key and not provider.key_optional:
        raise ValueError(
            f"Model '{model}' needs the {provider.api_key_env} environment variable."
        )

    from pd_runner.llm.openai_client import OpenAICompatClient

    return OpenAICompatClient(
        system_prompt=system_prompt,
        tools=tools,
        model=model,
        max_iterations=max_iterations,
        max_tokens=max_tokens,
        thinking_effort=thinking_effort,
        provider=provider,
        api_key=api_key,
    )

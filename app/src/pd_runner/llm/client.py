"""Minimal provider-agnostic LLM client interface (placeholder)."""

from __future__ import annotations


class LLMClient:
    def generate(self, prompt: str) -> str:
        raise NotImplementedError("LLM client implementation is not wired yet")

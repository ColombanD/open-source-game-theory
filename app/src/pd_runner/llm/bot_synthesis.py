"""Placeholder for generating candidate bot Lean code with an LLM."""

from __future__ import annotations

from pd_runner.llm.client import LLMClient
from pd_runner.llm.prompts import bot_synthesis_prompt


def synthesize_bot(client: LLMClient, task: str) -> str:
    prompt = bot_synthesis_prompt(task)
    return client.generate(prompt)

"""Prompt templates for future bot synthesis and analysis."""

from __future__ import annotations


def bot_synthesis_prompt(task: str) -> str:
    return f"Synthesize a Lean bot strategy for this task: {task}" + "\nReturn Lean code only."

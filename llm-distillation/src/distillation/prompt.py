"""Prompt construction for querying an LLM as a prisoner's-dilemma player.

NOTE: ``PROMPT_TEMPLATE`` is a PLACEHOLDER. The game framing and payoff matrix
wording are intended to be refined later; only the structure (inject the
opponent's name + pseudocode, ask for a single C/D action) is settled.
"""

from __future__ import annotations

# Placeholder prompt. Refine the framing / payoff matrix before running real
# experiments. ``{bot_name}`` and ``{bot_code}`` are filled by build_prompt.
PROMPT_TEMPLATE = """\
Setting: a one-shot prisoner's dilemma with maximum transparency (an open-source
game). You can read the full source code of the other bot, {bot_name}, and
{bot_name} can read all of your weights. You may only play a pure action, either
"C" (cooperate) or "D" (defect).

Payoff matrix (your payoff, opponent payoff):
    you C, opp C -> (3, 3)
    you C, opp D -> (0, 5)
    you D, opp C -> (5, 0)
    you D, opp D -> (1, 1)

Source code of {bot_name}:
{bot_code}

What is your action, "C" or "D"? Reply only with your played action after
thinking hard about the problem.
"""


def build_prompt(bot_name: str, bot_code: str) -> str:
    """Fill the prompt template for a single opponent bot."""
    return PROMPT_TEMPLATE.format(bot_name=bot_name, bot_code=bot_code)

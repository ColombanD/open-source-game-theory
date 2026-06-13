"""Prompt construction for querying an LLM as a prisoner's-dilemma player.

The prompt frames the open-source (max-transparency) one-shot PD, explains the
notation used in the opponent's source code (``simulate``, ``proof_search``, the
budget ``k``, probe-bot references), injects the opponent's pseudocode, and asks
the model to reason and end with a parseable ``My action <<A>>`` line.
"""

from __future__ import annotations

# ``{bot_name}`` and ``{bot_code}`` are filled by build_prompt. Keep the prose
# free of literal { } braces so str.format stays safe.
PROMPT_TEMPLATE = """\
You are playing a one-shot Prisoner's Dilemma under *maximum transparency* (an
"open-source" game): before either side moves, you can read the full source code
of the other bot, {bot_name}, and {bot_name} can read all of your weights. There
is a single simultaneous move and no repetition. You must commit to a pure
action -- either "C" (cooperate) or "D" (defect) -- never a randomized or mixed
strategy.

Payoff matrix (your payoff, opponent payoff):
    you C, opp C -> (3, 3)
    you C, opp D -> (0, 5)
    you D, opp C -> (5, 0)
    you D, opp D -> (1, 1)

Notation used in the source code (written as Python-like pseudocode):
  - C, D: the two pure actions, Cooperate and Defect.
  - opp: the opponent's source code, which the bot can read in full.
  - simulate(p, q): run program p against opponent q and return the action p
    plays. Transparency makes this possible -- a bot can execute the opponent's
    code against a probe to see what it would do.
  - proof_search(k, opp, hypothesis): a bounded, sound proof oracle. It returns
    True iff a proof of `hypothesis` (a statement about how `opp` behaves) can be
    found within a budget of k steps. Soundness means a True result is never
    wrong: if it returns True, the hypothesis really holds. A False result only
    means no proof was found within budget k.
  - k: the budget (number of steps) given to proof_search.
  - References to other bots (e.g. CooperateBot, DefectBot, MirrorBot) denote
    those programs' source code, used as fixed probes.

Source code of {bot_name}:
{bot_code}

Reply with your reasoning for your chosen action. Remember that you must output a
pure action, not a mixed strategy. Finally, on a new line, reply with
    My action <<A>>
where A is either C or D (for example, "My action <<C>>").
"""


def build_prompt(bot_name: str, bot_code: str) -> str:
    """Fill the prompt template for a single opponent bot."""
    return PROMPT_TEMPLATE.format(bot_name=bot_name, bot_code=bot_code)

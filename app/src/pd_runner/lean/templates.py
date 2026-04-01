from __future__ import annotations


def matchup_eval_template(left_bot: str, right_bot: str) -> str:
    """Lean snippet that evaluates the action pair for a chosen bot matchup."""
    return f"""import PrisonersDilemma.Models.OpenSourceBots

open PD
open PD.Models.OpenSourceBots

#eval playActions Bot.{left_bot} Bot.{right_bot}
"""

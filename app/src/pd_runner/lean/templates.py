from __future__ import annotations


def matchup_eval_template(
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> str:
    """Lean snippet that evaluates the action pair for a chosen bot matchup."""
    theorem_block = ""
    if claim_left_action is not None and claim_right_action is not None:
        theorem_block = f"""

theorem claimed_actions : ActionClaim Bot.{left_bot} Bot.{right_bot} {claim_left_action} {claim_right_action} := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]
"""

    return f"""import PrisonersDilemma.Models.OpenSourceBots

open PD
open PD.Action
open PD.Models.OpenSourceBots

{theorem_block}

#eval playActions Bot.{left_bot} Bot.{right_bot}
"""

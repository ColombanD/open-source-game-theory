from __future__ import annotations


def _known_action_claims(
    left_bot: str,
    right_bot: str,
    ) -> tuple[str, str, str] | None:
    """Return (theorem_name, left_action, right_action) for a known matchup, when available."""
    theorem_map: dict[tuple[str, str], tuple[str, str, str]] = {
        ("cooperateBot", "cooperateBot"): ("cc_actionClaim", "C", "C"),
        ("cooperateBot", "defectBot"): ("cd_actionClaim", "C", "D"),
        ("defectBot", "cooperateBot"): ("dc_actionClaim", "D", "C"),
        ("defectBot", "defectBot"): ("dd_actionClaim", "D", "D"),
        ("titForTat", "cooperateBot"): ("tft_c_actionClaim", "C", "C"),
        ("titForTat", "defectBot"): ("tft_d_actionClaim", "D", "D"),
        ("titForTat", "titForTat"): ("tft_tft_actionClaim", "C", "C"),
    }
    return theorem_map.get((left_bot, right_bot))


def select_action_claim_theorem(
    left_bot: str,
    right_bot: str,
    claim_left_action: str,
    claim_right_action: str,
) -> str | None:
    """Return a pre-proved theorem name for this exact ActionClaim, when available."""
    known = _known_action_claims(left_bot, right_bot)
    if known is None:
        return None
    theorem_name, expected_left_action, expected_right_action = known
    if (claim_left_action, claim_right_action) != (expected_left_action, expected_right_action):
        return None
    return theorem_name


def matchup_eval_template(
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> tuple[str, str | None]:
    """Lean snippet that evaluates the action pair for a chosen bot matchup."""
    theorem_block = ""
    proof_theorem_used: str | None = None
    if claim_left_action is None and claim_right_action is None:
        known = _known_action_claims(left_bot, right_bot)
        if known is not None:
            preproved, claim_left_action, claim_right_action = known
        else:
            preproved = None
    elif claim_left_action is not None and claim_right_action is not None:
        preproved = select_action_claim_theorem(
            left_bot,
            right_bot,
            claim_left_action,
            claim_right_action,
        )
    else:
        preproved = None

    if claim_left_action is not None and claim_right_action is not None:
        if preproved is not None:
            proof_theorem_used = f"PD.Proofs.OpenSourceBots.{preproved}"
            theorem_block = f"""

theorem claimed_actions : ActionClaim Bot.{left_bot} Bot.{right_bot} {claim_left_action} {claim_right_action} := by
  exact {preproved}
"""
        else:
            proof_theorem_used = "generated:unfold+simp"
            theorem_block = f"""

theorem claimed_actions : ActionClaim Bot.{left_bot} Bot.{right_bot} {claim_left_action} {claim_right_action} := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]
"""

    script = f"""import PrisonersDilemma.Models.OpenSourceBots
import PrisonersDilemma.Proofs.OpenSourceBots

open PD
open PD.Action
open PD.Models.OpenSourceBots
open PD.Proofs.OpenSourceBots

{theorem_block}

#eval playActions Bot.{left_bot} Bot.{right_bot}
"""
    return script, proof_theorem_used

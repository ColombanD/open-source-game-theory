from __future__ import annotations

import re
from pathlib import Path


def _discover_action_claim_theorems(proofs_dir: Path) -> dict[tuple[str, str], tuple[str, str, str]]:
    """Scan Lean proof files and discover ActionClaim theorems.
    
    Returns a mapping of (left_bot, right_bot) -> (theorem_name, left_action, right_action).
    """
    theorem_map: dict[tuple[str, str], tuple[str, str, str]] = {}
    
    # Pattern to match: theorem name_actionClaim : ActionClaim Bot.leftBot Bot.rightBot ACTION ACTION
    pattern = r'theorem\s+(\w+)\s*:\s*ActionClaim\s+Bot\.(\w+)\s+Bot\.(\w+)\s+([CD])\s+([CD])'
    
    for lean_file in proofs_dir.glob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        matches = re.findall(pattern, content)
        
        for theorem_name, left_bot, right_bot, left_action, right_action in matches:
            theorem_map[(left_bot, right_bot)] = (theorem_name, left_action, right_action)
    
    return theorem_map


# Get the proofs directory relative to this file
# Path structure: app/src/pd_runner/lean/templates.py
# We need to go to: ../../../.. (to workspace root) / engine / PrisonersDilemma / Proofs
_PROOFS_DIR = Path(__file__).parent.parent.parent.parent.parent / "engine" / "PrisonersDilemma" / "Proofs"
_ACTION_CLAIM_THEOREMS = _discover_action_claim_theorems(_PROOFS_DIR) if _PROOFS_DIR.exists() else {}



def select_action_claim_theorem(
    left_bot: str,
    right_bot: str,
    claim_left_action: str,
    claim_right_action: str,
) -> tuple[str, bool] | None:
    """Return a pre-proved theorem for this ActionClaim, checking both orders.
    
    Returns (theorem_name, is_reversed) where:
    - is_reversed=False: theorem proves (left_bot, right_bot) directly
    - is_reversed=True: theorem proves (right_bot, left_bot) with swapped actions
    """
    # Try direct order first
    entry = _ACTION_CLAIM_THEOREMS.get((left_bot, right_bot))
    if entry is not None:
        theorem_name, expected_left_action, expected_right_action = entry
        if (claim_left_action, claim_right_action) == (expected_left_action, expected_right_action):
            return (theorem_name, False)
    
    # Try reverse order: if (right_bot, left_bot) proves (x, y),
    # and we want (left_bot, right_bot) with swapped actions (y, x)
    entry_reversed = _ACTION_CLAIM_THEOREMS.get((right_bot, left_bot))
    if entry_reversed is not None:
        theorem_name, expected_left_action, expected_right_action = entry_reversed
        # Right_bot's action becomes left_bot's action in reversed order
        if (claim_left_action, claim_right_action) == (expected_right_action, expected_left_action):
            return (theorem_name, True)
    
    return None


def matchup_eval_template(
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> tuple[str, str | None, bool]:
    """Lean snippet that evaluates the action pair for a chosen bot matchup.
    
    Returns (script, proof_theorem_used, actions_are_swapped) where:
    - script: Lean code to evaluate
    - proof_theorem_used: which theorem was used, if any
    - actions_are_swapped: whether the returned actions should be swapped by the caller
    """
    theorem_block = ""
    proof_theorem_used: str | None = None
    actions_are_swapped = False
    
    # Determine if we should look up a pre-proved theorem
    if claim_left_action is None and claim_right_action is None:
        # Auto-detect from available theorems (try direct order first)
        entry = _ACTION_CLAIM_THEOREMS.get((left_bot, right_bot))
        if entry is not None:
            theorem_name, claim_left_action, claim_right_action = entry
        else:
            # Try reverse order
            entry_reversed = _ACTION_CLAIM_THEOREMS.get((right_bot, left_bot))
            if entry_reversed is not None:
                theorem_name, rev_left_action, rev_right_action = entry_reversed
                # Swap the actions for the requested pairing
                claim_left_action, claim_right_action = rev_right_action, rev_left_action
                actions_are_swapped = True
    
    # Determine which pairing to evaluate in Lean
    eval_left_bot = left_bot
    eval_right_bot = right_bot
    eval_left_action = claim_left_action
    eval_right_action = claim_right_action
    
    # Generate theorem block if we have a claim
    if claim_left_action is not None and claim_right_action is not None:
        result = select_action_claim_theorem(
            left_bot,
            right_bot,
            claim_left_action,
            claim_right_action,
        )
        
        if result is not None:
            preproved, is_reversed = result
            
            if is_reversed:
                # Use the reverse pairing for the Lean eval
                eval_left_bot = right_bot
                eval_right_bot = left_bot
                eval_left_action = claim_right_action
                eval_right_action = claim_left_action
                actions_are_swapped = True
            
            # Find which proof file this theorem is in
            proof_file = None
            for lean_file in _PROOFS_DIR.glob("*.lean"):
                if preproved in lean_file.read_text(encoding="utf-8"):
                    proof_file = lean_file.stem
                    break
            
            # Use fully qualified theorem name
            qualified_theorem = f"PD.Proofs.{proof_file}.{preproved}" if proof_file else preproved
            proof_theorem_used = qualified_theorem
            theorem_block = f"""

theorem claimed_actions : ActionClaim Bot.{eval_left_bot} Bot.{eval_right_bot} {eval_left_action} {eval_right_action} := by
  exact {qualified_theorem}
"""
        else:
            proof_theorem_used = "generated:unfold+simp"
            theorem_block = f"""

theorem claimed_actions : ActionClaim Bot.{eval_left_bot} Bot.{eval_right_bot} {eval_left_action} {eval_right_action} := by
  unfold ActionClaim playActions
  simp [ProgramModel.action]
"""

    # Build imports
    imports = """import PrisonersDilemma.Models.BotUniverse
import PrisonersDilemma.Pipeline"""
    
    # Add proof file imports if there's a theorem to prove
    if claim_left_action is not None and claim_right_action is not None:
        result = select_action_claim_theorem(
            left_bot,
            right_bot,
            claim_left_action,
            claim_right_action,
        )
        if result is not None:
            preproved, is_reversed = result
            # Find and import the proof file
            for lean_file in _PROOFS_DIR.glob("*.lean"):
                if preproved in lean_file.read_text(encoding="utf-8"):
                    imports += f"\nimport PrisonersDilemma.Proofs.{lean_file.stem}"
                    break

    script = f"""{imports}

open PD
open PD.Action
open PD.Models.BotUniverse

{theorem_block}

#eval playActions Bot.{eval_left_bot} Bot.{eval_right_bot}
"""
    return script, proof_theorem_used, actions_are_swapped


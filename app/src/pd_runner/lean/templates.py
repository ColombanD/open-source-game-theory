from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

DEFAULT_EVAL_FUEL = 20


@dataclass(frozen=True)
class OutcomeTheorem:
    name: str
    module: str
    left_bot: str
    right_bot: str
    left_action: str
    right_action: str
    fuel_param: str
    fuel_expr: str

    @property
    def qualified_name(self) -> str:
        return f"PDNew.Theorems.{self.name}"

    @property
    def concrete_fuel_expr(self) -> str:
        return re.sub(rf"\b{re.escape(self.fuel_param)}\b", "0", self.fuel_expr)


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_ENGINE_PD_DIR = _workspace_root() / "engine" / "PrisonersDilemma"
_BOTS_DIR = _ENGINE_PD_DIR / "Bots"
_THEOREMS_DIR = _ENGINE_PD_DIR / "Theorems"


def _discover_bot_names(bots_dir: Path) -> set[str]:
    pattern = re.compile(r"\bdef\s+([A-Za-z_]\w*)\b")
    names: set[str] = set()

    if not bots_dir.exists():
        return names

    for lean_file in bots_dir.glob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        names.update(pattern.findall(content))

    return names


def _legacy_bot_aliases(bot_names: set[str]) -> dict[str, str]:
    aliases: dict[str, str] = {}
    for name in bot_names:
        aliases[name] = name
        aliases[name.lower()] = name
        aliases[f"{name[0].lower()}{name[1:]}"] = name

    aliases.update(
        {
            "cooperateBot": "CooperateBot",
            "defectBot": "DefectBot",
            "dBot": "DBot",
            "eBot": "EBot",
            "oBot": "OBot",
            "cupodBot": "CupodBot",
            "dupocBot": "DupocBot",
            "mirrorBot": "MirrorBot",
            "titForTatBot": "TitForTatBot",
        }
    )
    return {alias: target for alias, target in aliases.items() if target in bot_names}


def normalize_bot_name(name: str) -> str:
    return _BOT_ALIASES.get(name, name)


def _discover_outcome_theorems(theorems_dir: Path) -> dict[tuple[str, str], OutcomeTheorem]:
    """Scan Lean theorem files and discover concrete `outcome` theorems."""
    theorem_map: dict[tuple[str, str], OutcomeTheorem] = {}

    if not theorems_dir.exists():
        return theorem_map

    pattern = re.compile(
        r"theorem\s+(\w+)\s*"
        r"\(\s*(\w+)\s*:\s*Nat\s*\)\s*:\s*"
        r"outcome\s+(.+?)\s+"
        r"([A-Za-z_]\w*)\s+([A-Za-z_]\w*)\s*=\s*"
        r"some\s+\(\.([CD]),\s*\.([CD])\)",
        re.DOTALL,
    )

    for lean_file in theorems_dir.glob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        for match in pattern.finditer(content):
            theorem_name = match.group(1)
            fuel_param = match.group(2)
            fuel_expr = " ".join(match.group(3).split())
            left_bot = match.group(4)
            right_bot = match.group(5)
            left_action = match.group(6)
            right_action = match.group(7)

            theorem_map[(left_bot, right_bot)] = OutcomeTheorem(
                name=theorem_name,
                module=lean_file.stem,
                left_bot=left_bot,
                right_bot=right_bot,
                left_action=left_action,
                right_action=right_action,
                fuel_param=fuel_param,
                fuel_expr=fuel_expr,
            )

    return theorem_map


_BOT_NAMES = _discover_bot_names(_BOTS_DIR)
_BOT_ALIASES = _legacy_bot_aliases(_BOT_NAMES)
_OUTCOME_THEOREMS = _discover_outcome_theorems(_THEOREMS_DIR)


def select_outcome_theorem(
    left_bot: str,
    right_bot: str,
    claim_left_action: str,
    claim_right_action: str,
) -> tuple[OutcomeTheorem, bool] | None:
    """Return a pre-proved theorem for this outcome, checking both orders."""
    left_bot = normalize_bot_name(left_bot)
    right_bot = normalize_bot_name(right_bot)

    entry = _OUTCOME_THEOREMS.get((left_bot, right_bot))
    if entry is not None:
        if (claim_left_action, claim_right_action) == (entry.left_action, entry.right_action):
            return (entry, False)

    entry_reversed = _OUTCOME_THEOREMS.get((right_bot, left_bot))
    if entry_reversed is not None:
        if (claim_left_action, claim_right_action) == (
            entry_reversed.right_action,
            entry_reversed.left_action,
        ):
            return (entry_reversed, True)

    return None


def select_action_claim_theorem(
    left_bot: str,
    right_bot: str,
    claim_left_action: str,
    claim_right_action: str,
) -> tuple[str, bool] | None:
    """Backward-compatible wrapper around new `outcome` theorem discovery."""
    result = select_outcome_theorem(left_bot, right_bot, claim_left_action, claim_right_action)
    if result is None:
        return None

    theorem, is_reversed = result
    return theorem.name, is_reversed


def _auto_select_outcome(left_bot: str, right_bot: str) -> tuple[OutcomeTheorem, bool] | None:
    entry = _OUTCOME_THEOREMS.get((left_bot, right_bot))
    if entry is not None:
        return (entry, False)

    entry_reversed = _OUTCOME_THEOREMS.get((right_bot, left_bot))
    if entry_reversed is not None:
        return (entry_reversed, True)

    return None


def matchup_eval_template(
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> tuple[str, str | None, bool]:
    """Lean snippet that evaluates the action pair for a chosen bot matchup."""
    left_bot = normalize_bot_name(left_bot)
    right_bot = normalize_bot_name(right_bot)

    theorem: OutcomeTheorem | None = None
    actions_are_swapped = False

    if claim_left_action is not None and claim_right_action is not None:
        selected = select_outcome_theorem(
            left_bot,
            right_bot,
            claim_left_action,
            claim_right_action,
        )
        if selected is not None:
            theorem, actions_are_swapped = selected
    else:
        selected = _auto_select_outcome(left_bot, right_bot)
        if selected is not None:
            theorem, actions_are_swapped = selected

    eval_left_bot = left_bot
    eval_right_bot = right_bot
    eval_fuel = str(DEFAULT_EVAL_FUEL)
    theorem_block = ""
    proof_theorem_used: str | None = None

    if theorem is not None:
        eval_left_bot = theorem.left_bot
        eval_right_bot = theorem.right_bot
        eval_fuel = theorem.concrete_fuel_expr
        proof_theorem_used = theorem.qualified_name
        theorem_block = f"""

theorem claimed_outcome :
    outcome {eval_fuel} {eval_left_bot} {eval_right_bot} =
      some (.{theorem.left_action}, .{theorem.right_action}) := by
  exact {theorem.qualified_name} 0
"""
        eval_line = f"#eval ((Action.{theorem.left_action}, Action.{theorem.right_action}) : Outcome)"
    else:
        eval_line = f"#check outcome {eval_fuel} {eval_left_bot} {eval_right_bot}"

    script = f"""import PrisonersDilemma

open PDNew
open PDNew.Bots
open PDNew.Theorems

{theorem_block}

{eval_line}
"""
    return script, proof_theorem_used, actions_are_swapped

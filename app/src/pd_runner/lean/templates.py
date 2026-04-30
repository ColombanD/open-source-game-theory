from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

DEFAULT_EVAL_FUEL = 20


@dataclass(frozen=True)
class BotDef:
    name: str
    nat_params: tuple[str, ...] = ()


@dataclass(frozen=True)
class BotExpr:
    name: str
    arg: str | None = None

    @property
    def has_existential_arg(self) -> bool:
        return self.arg == "?"

    def lean(self) -> str:
        if self.arg is None:
            return self.name
        if self.arg == "?":
            raise ValueError("existential bot expression has no concrete Lean term")
        return f"({self.name} {self.arg})"


@dataclass(frozen=True)
class BotPattern:
    name: str
    arg_param: str | None = None

    def lean(self, substitutions: dict[str, str]) -> str:
        if self.arg_param is None:
            return self.name
        return f"({self.name} {substitutions[self.arg_param]})"

    def existential_lean(self) -> str:
        if self.arg_param is None:
            return self.name
        return f"({self.name} {self.arg_param})"


@dataclass(frozen=True)
class UniversalOutcomeTheorem:
    name: str
    module: str
    params: tuple[str, ...]
    left_bot: BotPattern
    right_bot: BotPattern
    left_action: str
    right_action: str
    fuel_param: str
    fuel_expr: str

    @property
    def qualified_name(self) -> str:
        return f"PDNew.Theorems.{self.name}"

    def concrete_fuel_expr(self, substitutions: dict[str, str]) -> str:
        return _substitute_identifiers(self.fuel_expr, substitutions | {self.fuel_param: "0"})

    def exact_args(self, substitutions: dict[str, str]) -> str:
        args = [substitutions.get(param, "0") for param in self.params]
        return " ".join(args)


@dataclass(frozen=True)
class ExistentialOutcomeTheorem:
    name: str
    module: str
    params: tuple[str, ...]
    exists_param: str
    left_bot: BotPattern
    right_bot: BotPattern
    left_action: str
    right_action: str
    fuel_param: str
    fuel_expr: str

    @property
    def qualified_name(self) -> str:
        return f"PDNew.Theorems.{self.name}"

    def concrete_fuel_expr(self) -> str:
        return _substitute_identifiers(self.fuel_expr, {self.fuel_param: "0"})

    def exact_args(self) -> str:
        return " ".join("0" for _ in self.params)


SelectedTheorem = UniversalOutcomeTheorem | ExistentialOutcomeTheorem


@dataclass(frozen=True)
class TheoremSelection:
    theorem: SelectedTheorem
    is_reversed: bool
    substitutions: dict[str, str]
    result_kind: str
    witness: str | None = None


def _workspace_root() -> Path:
    return Path(__file__).resolve().parents[4]


_ENGINE_PD_DIR = _workspace_root() / "engine" / "PrisonersDilemma"
_BOTS_DIR = _ENGINE_PD_DIR / "Bots"
_THEOREMS_DIR = _ENGINE_PD_DIR / "Theorems"


def _substitute_identifiers(expr: str, substitutions: dict[str, str]) -> str:
    result = expr
    for name, value in substitutions.items():
        result = re.sub(rf"\b{re.escape(name)}\b", value, result)
    return result


def _discover_bot_defs(bots_dir: Path) -> dict[str, BotDef]:
    pattern = re.compile(r"\bdef\s+([A-Za-z_]\w*)\s*(.*?)\s*:\s*Prog\b", re.DOTALL)
    param_pattern = re.compile(r"\(([^():]+?)\s*:\s*Nat\s*\)")
    defs: dict[str, BotDef] = {}

    if not bots_dir.exists():
        return defs

    for lean_file in bots_dir.glob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        for match in pattern.finditer(content):
            name = match.group(1)
            params: list[str] = []
            for params_match in param_pattern.finditer(match.group(2)):
                params.extend(params_match.group(1).split())
            defs[name] = BotDef(name=name, nat_params=tuple(params))

    return defs


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


def available_bot_names() -> tuple[str, ...]:
    return tuple(sorted(_BOT_DEFS))


def format_available_bot_names() -> str:
    return ", ".join(available_bot_names())


def parse_bot_expr(text: str) -> BotExpr:
    name, sep, arg = text.partition(":")
    normalized_name = normalize_bot_name(name)
    if normalized_name not in _BOT_DEFS:
        raise ValueError(f"unknown bot: {name}. available bots: {format_available_bot_names()}")
    if not sep:
        return BotExpr(normalized_name)
    if arg != "?" and not arg.isdecimal():
        raise ValueError(f"invalid bot parameter: {text}. expected a natural number or ?")
    if arg is not None and not _BOT_DEFS[normalized_name].nat_params:
        raise ValueError(f"bot does not take a parameter: {normalized_name}")
    return BotExpr(normalized_name, arg)


def _parse_params(params_text: str) -> tuple[str, ...]:
    params: list[str] = []
    for group in re.finditer(r"\(([^():]+?)\s*:\s*Nat\s*\)", params_text):
        params.extend(group.group(1).split())
    return tuple(params)


def _split_lean_terms(text: str) -> list[str]:
    terms: list[str] = []
    start: int | None = None
    depth = 0

    for idx, char in enumerate(text.strip()):
        if start is None and not char.isspace():
            start = idx
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char.isspace() and depth == 0 and start is not None:
            terms.append(text.strip()[start:idx])
            start = None

    stripped = text.strip()
    if start is not None:
        terms.append(stripped[start:])
    return terms


def _parse_bot_pattern(term: str) -> BotPattern | None:
    bare = re.fullmatch(r"([A-Za-z_]\w*)", term)
    if bare:
        return BotPattern(bare.group(1))

    parameterized = re.fullmatch(r"\(([A-Za-z_]\w*)\s+([A-Za-z_]\w*)\)", term)
    if parameterized:
        return BotPattern(parameterized.group(1), parameterized.group(2))

    return None


def _parse_outcome_terms(outcome_terms: str) -> tuple[str, BotPattern, BotPattern] | None:
    terms = _split_lean_terms(outcome_terms)
    if len(terms) != 3:
        return None
    left = _parse_bot_pattern(terms[1])
    right = _parse_bot_pattern(terms[2])
    if left is None or right is None:
        return None
    return terms[0], left, right


def _fuel_param(params: tuple[str, ...], fuel_expr: str) -> str | None:
    for param in reversed(params):
        if re.search(rf"\b{re.escape(param)}\b", fuel_expr):
            return param
    return None


def _discover_outcome_theorems(
    theorems_dir: Path,
) -> tuple[list[UniversalOutcomeTheorem], list[ExistentialOutcomeTheorem]]:
    universal: list[UniversalOutcomeTheorem] = []
    existential: list[ExistentialOutcomeTheorem] = []

    if not theorems_dir.exists():
        return universal, existential

    theorem_pattern = re.compile(
        r"theorem\s+(\w+)\s*"
        r"((?:\([^)]*:\s*Nat\s*\)\s*)+)\s*:\s*"
        r"(.*?)\s*:=\s*by",
        re.DOTALL,
    )
    universal_pattern = re.compile(
        r"outcome\s+(.+?)\s*=\s*some\s+\(\.([CD]),\s*\.([CD])\)",
        re.DOTALL,
    )
    existential_pattern = re.compile(
        r"∃\s+(\w+),\s*outcome\s+(.+?)\s*=\s*some\s+\(\.([CD]),\s*\.([CD])\)",
        re.DOTALL,
    )

    for lean_file in theorems_dir.glob("*.lean"):
        content = lean_file.read_text(encoding="utf-8")
        for theorem_match in theorem_pattern.finditer(content):
            theorem_name = theorem_match.group(1)
            params = _parse_params(theorem_match.group(2))
            statement = " ".join(theorem_match.group(3).split())

            exists_match = existential_pattern.fullmatch(statement)
            if exists_match:
                exists_param = exists_match.group(1)
                parsed = _parse_outcome_terms(exists_match.group(2))
                if parsed is None:
                    continue
                fuel_expr, left_bot, right_bot = parsed
                fuel = _fuel_param(params, fuel_expr)
                if fuel is None:
                    continue
                existential.append(
                    ExistentialOutcomeTheorem(
                        name=theorem_name,
                        module=lean_file.stem,
                        params=params,
                        exists_param=exists_param,
                        left_bot=left_bot,
                        right_bot=right_bot,
                        left_action=exists_match.group(3),
                        right_action=exists_match.group(4),
                        fuel_param=fuel,
                        fuel_expr=fuel_expr,
                    )
                )
                continue

            universal_match = universal_pattern.fullmatch(statement)
            if universal_match:
                parsed = _parse_outcome_terms(universal_match.group(1))
                if parsed is None:
                    continue
                fuel_expr, left_bot, right_bot = parsed
                fuel = _fuel_param(params, fuel_expr)
                if fuel is None:
                    continue
                universal.append(
                    UniversalOutcomeTheorem(
                        name=theorem_name,
                        module=lean_file.stem,
                        params=params,
                        left_bot=left_bot,
                        right_bot=right_bot,
                        left_action=universal_match.group(2),
                        right_action=universal_match.group(3),
                        fuel_param=fuel,
                        fuel_expr=fuel_expr,
                    )
                )

    return universal, existential


def _match_pattern(
    pattern: BotPattern,
    expr: BotExpr,
    substitutions: dict[str, str],
    allow_existential: bool,
) -> dict[str, str] | None:
    if pattern.name != expr.name:
        return None

    if pattern.arg_param is None:
        return substitutions if expr.arg is None else None

    if expr.arg is None:
        return None
    if expr.arg == "?":
        if not allow_existential:
            return None
        current = substitutions.get(pattern.arg_param)
        return substitutions | {pattern.arg_param: current or "0"}

    current = substitutions.get(pattern.arg_param)
    if current is not None and current != expr.arg:
        return None
    return substitutions | {pattern.arg_param: expr.arg}


def _select_universal(
    left: BotExpr,
    right: BotExpr,
    claim_left_action: str | None,
    claim_right_action: str | None,
) -> TheoremSelection | None:
    allows_wildcard = left.has_existential_arg or right.has_existential_arg
    result_kind = "all_parameters" if allows_wildcard else "concrete"
    witness = "any" if allows_wildcard else None

    for theorem in _UNIVERSAL_OUTCOME_THEOREMS:
        direct_subst = _match_pattern(theorem.left_bot, left, {}, allow_existential=allows_wildcard)
        if direct_subst is not None:
            direct_subst = _match_pattern(
                theorem.right_bot,
                right,
                direct_subst,
                allow_existential=allows_wildcard,
            )
        if direct_subst is not None and _actions_match(
            theorem.left_action,
            theorem.right_action,
            claim_left_action,
            claim_right_action,
        ):
            return TheoremSelection(theorem, False, direct_subst, result_kind, witness)

        reversed_subst = _match_pattern(theorem.left_bot, right, {}, allow_existential=allows_wildcard)
        if reversed_subst is not None:
            reversed_subst = _match_pattern(
                theorem.right_bot,
                left,
                reversed_subst,
                allow_existential=allows_wildcard,
            )
        if reversed_subst is not None and _actions_match(
            theorem.right_action,
            theorem.left_action,
            claim_left_action,
            claim_right_action,
        ):
            return TheoremSelection(theorem, True, reversed_subst, result_kind, witness)

    return None


def _select_existential(
    left: BotExpr,
    right: BotExpr,
    claim_left_action: str | None,
    claim_right_action: str | None,
) -> TheoremSelection | None:
    if not (left.has_existential_arg or right.has_existential_arg):
        return None

    for theorem in _EXISTENTIAL_OUTCOME_THEOREMS:
        direct_subst = _match_pattern(theorem.left_bot, left, {}, allow_existential=True)
        if direct_subst is not None:
            direct_subst = _match_pattern(theorem.right_bot, right, direct_subst, allow_existential=True)
        if direct_subst is not None and _actions_match(
            theorem.left_action,
            theorem.right_action,
            claim_left_action,
            claim_right_action,
        ):
            return TheoremSelection(theorem, False, direct_subst, "exists_parameter", None)

        reversed_subst = _match_pattern(theorem.left_bot, right, {}, allow_existential=True)
        if reversed_subst is not None:
            reversed_subst = _match_pattern(theorem.right_bot, left, reversed_subst, allow_existential=True)
        if reversed_subst is not None and _actions_match(
            theorem.right_action,
            theorem.left_action,
            claim_left_action,
            claim_right_action,
        ):
            return TheoremSelection(theorem, True, reversed_subst, "exists_parameter", None)

    return None


def _actions_match(
    theorem_left: str,
    theorem_right: str,
    claim_left: str | None,
    claim_right: str | None,
) -> bool:
    if claim_left is None and claim_right is None:
        return True
    return (claim_left, claim_right) == (theorem_left, theorem_right)


_BOT_DEFS = _discover_bot_defs(_BOTS_DIR)
_BOT_ALIASES = _legacy_bot_aliases(set(_BOT_DEFS))
_UNIVERSAL_OUTCOME_THEOREMS, _EXISTENTIAL_OUTCOME_THEOREMS = _discover_outcome_theorems(_THEOREMS_DIR)


def select_outcome_theorem(
    left_bot: str,
    right_bot: str,
    claim_left_action: str,
    claim_right_action: str,
) -> tuple[UniversalOutcomeTheorem, bool] | None:
    """Return a concrete pre-proved outcome theorem, checking both orders."""
    selection = _select_universal(
        parse_bot_expr(left_bot),
        parse_bot_expr(right_bot),
        claim_left_action,
        claim_right_action,
    )
    if selection is None or not isinstance(selection.theorem, UniversalOutcomeTheorem):
        return None
    return selection.theorem, selection.is_reversed


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


def _select_theorem(
    left: BotExpr,
    right: BotExpr,
    claim_left_action: str | None,
    claim_right_action: str | None,
) -> TheoremSelection | None:
    return _select_universal(left, right, claim_left_action, claim_right_action) or _select_existential(
        left,
        right,
        claim_left_action,
        claim_right_action,
    )


def _lean_for_requested_expr(expr: BotExpr) -> str:
    if expr.has_existential_arg:
        raise ValueError("existential bot expression cannot be used as a concrete Lean term")
    return expr.lean()


def matchup_eval_template(
    left_bot: str,
    right_bot: str,
    claim_left_action: str | None = None,
    claim_right_action: str | None = None,
) -> tuple[str, str | None, bool, str, str | None]:
    """Lean snippet that checks the action pair for a chosen bot matchup."""
    left_expr = parse_bot_expr(left_bot)
    right_expr = parse_bot_expr(right_bot)

    selection = _select_theorem(left_expr, right_expr, claim_left_action, claim_right_action)
    theorem_block = ""
    proof_theorem_used: str | None = None
    actions_are_swapped = False
    result_kind = "concrete"
    witness: str | None = None
    eval_line = ""

    if selection is not None:
        theorem = selection.theorem
        actions_are_swapped = selection.is_reversed
        result_kind = selection.result_kind
        witness = selection.witness
        proof_theorem_used = theorem.qualified_name

        if isinstance(theorem, UniversalOutcomeTheorem):
            eval_fuel = theorem.concrete_fuel_expr(selection.substitutions)
            eval_left_bot = theorem.left_bot.lean(selection.substitutions)
            eval_right_bot = theorem.right_bot.lean(selection.substitutions)
            exact_args = theorem.exact_args(selection.substitutions)
            theorem_block = f"""

theorem claimed_outcome :
    outcome {eval_fuel} {eval_left_bot} {eval_right_bot} =
      some (.{theorem.left_action}, .{theorem.right_action}) := by
  exact {theorem.qualified_name} {exact_args}
"""
        else:
            eval_fuel = theorem.concrete_fuel_expr()
            eval_left_bot = theorem.left_bot.existential_lean()
            eval_right_bot = theorem.right_bot.existential_lean()
            exact_args = theorem.exact_args()
            theorem_block = f"""

theorem claimed_exists_outcome :
    ∃ {theorem.exists_param}, outcome {eval_fuel} {eval_left_bot} {eval_right_bot} =
      some (.{theorem.left_action}, .{theorem.right_action}) := by
  exact {theorem.qualified_name} {exact_args}
"""

        eval_line = f"#eval ((Action.{theorem.left_action}, Action.{theorem.right_action}) : Outcome)"
    else:
        if not left_expr.has_existential_arg and not right_expr.has_existential_arg:
            eval_line = (
                f"#check outcome {DEFAULT_EVAL_FUEL} "
                f"{_lean_for_requested_expr(left_expr)} {_lean_for_requested_expr(right_expr)}"
            )

    script = f"""import PrisonersDilemma

open PDNew
open PDNew.Bots
open PDNew.Theorems

{theorem_block}

{eval_line}
"""
    return script, proof_theorem_used, actions_are_swapped, result_kind, witness

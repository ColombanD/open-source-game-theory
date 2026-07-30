"""Structured proof-search verdicts and the deterministic exit checks.

This module owns the proof-search data types (`ProofRequest`, `ProofResult`,
`ProofSearchError`, `ProofOutcome`) and every static source check the exit
verification and the library writer share. It has no LLM dependencies beyond
the `UsageTotals` accounting type, so both `llm.tools` and the services can
import it without cycles. `services.proof_service` re-exports the public
names for backward compatibility.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Literal

from pd_runner import settings
from pd_runner.llm.client import UsageTotals
from pd_runner.settings import EvalGuard

VerdictKind = Literal["proved", "open_bistable", "open_blocked", "constructor_proposed"]
OutcomeKind = Literal[
    "proved", "open_bistable", "open_blocked", "constructor_proposed", "exhausted", "error"
]

VERDICT_KINDS: tuple[str, ...] = (
    "proved", "open_bistable", "open_blocked", "constructor_proposed",
)


# ---------------------------------------------------------------------------
# Request / result types (moved from proof_service; re-exported there)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class ProofRequest:
    left_bot: str
    right_bot: str
    left_action: str | None = None   # None → agent must discover the outcome
    right_action: str | None = None  # None → agent must discover the outcome
    fuel: int | None = None          # None → agent must pick a suitable fuel
    max_iterations: int = settings.DEFAULT_MAX_ITERATIONS  # turns per episode
    max_tokens: int = settings.DEFAULT_MAX_TOKENS
    thinking_effort: str = settings.DEFAULT_THINKING_EFFORT
    model: str = settings.DEFAULT_MODEL
    exclude_bots: frozenset[str] = frozenset()
    # Explicit split of exclude_bots' two concerns (leak vs mutation). When
    # None, it is derived from exclude_bots exactly as the old flag implied.
    eval_guard: EvalGuard | None = None
    max_episodes: int | None = None  # None → settings default

    @property
    def guard(self) -> EvalGuard:
        if self.eval_guard is not None:
            return self.eval_guard
        return EvalGuard.from_exclude_bots(self.exclude_bots)


@dataclass(frozen=True)
class ProofResult:
    left_bot: str
    right_bot: str
    left_action: str | None   # None when outcome is provably none (non-terminating)
    right_action: str | None
    lean_source: str
    iterations_used: int


@dataclass(frozen=True)
class ProofOutcome:
    """The structured result of one proof search — every terminal, success or not."""

    left_bot: str
    right_bot: str
    kind: OutcomeKind
    lean_source: str | None = None       # verified source; only for kind == "proved"
    left_action: str | None = None       # (None, None) also covers `= none` theorems
    right_action: str | None = None
    explanation: str = ""                # verdict explanation / blocked wall / error message
    proposal_name: str | None = None     # for kind == "constructor_proposed"
    episodes_used: int = 0
    turns_used: int = 0
    tool_calls_used: int = 0
    usage: UsageTotals = field(default_factory=UsageTotals)
    notebook: str = ""                   # final lab-notebook text (thesis data)

    @property
    def proved(self) -> bool:
        return self.kind == "proved"

    def legacy_error_kind(self) -> str:
        """Map to the ProofSearchError.kind strings the pre-episode API used."""
        if self.kind == "constructor_proposed":
            return "open_constructor_proposed"
        if self.kind in ("open_blocked", "open_bistable"):
            return self.kind
        if self.kind == "exhausted":
            return "no_output"
        return "error"


class ProofSearchError(RuntimeError):
    """Raised when proof search fails. Carries iterations_used and a result kind.

    `kind` distinguishes designed ladder terminals from genuine failures:
      - "open_constructor_proposed": OUTCOME OPEN with a Tier-2 proposal filed
      - "open_blocked": OUTCOME OPEN — BLOCKED: the outcome is semantically
        DETERMINED but its negative side (a ¬Pf census) is beyond the current
        exclusion kernels (e.g. the false-probe/recursive-avoid-set wall)
        (a *successful* escalation, pending human review)
      - "open_bistable": bare OUTCOME OPEN (genuinely undetermined matchup)
      - "no_output": the agent produced neither a proof nor an OPEN verdict
      - "error": parse failures and unexpected exceptions

    `outcome` carries the full structured ProofOutcome when available, so
    exception-path callers can read rich data without message parsing.
    """

    def __init__(
        self,
        message: str,
        *,
        iterations_used: int = 0,
        kind: str = "error",
        outcome: ProofOutcome | None = None,
    ) -> None:
        super().__init__(message)
        self.iterations_used = iterations_used
        self.kind = kind
        self.outcome = outcome


# ---------------------------------------------------------------------------
# Static source checks (moved from proof_service; shared by tools, exit
# verification, and the library writer)
# ---------------------------------------------------------------------------

_NONE_OUTCOME_RE = re.compile(r"outcome\s+\S.*?=\s*none\b", re.DOTALL)


def extract_actions_from_source(lean_source: str) -> tuple[str | None, str | None] | None:
    """Parse the action pair from a proven theorem statement.

    Returns:
        (action_left, action_right) for `= some (.X, .Y)` theorems.
        (None, None) for `= none` theorems (provably non-terminating pairs).
        None if no recognizable outcome pattern is found.
    """
    match = re.search(r"=\s*some\s*\(\.([CD]),\s*\.([CD])\)", lean_source)
    if match:
        return match.group(1), match.group(2)
    if _NONE_OUTCOME_RE.search(lean_source):
        return None, None
    return None


_BOT_DEF_RE = re.compile(r"^\s*def\s+(\w+)\s*:\s*Prog\b", re.MULTILINE)


_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_'!?]*)",
    re.MULTILINE,
)


def find_library_name_collisions(
    lean_source: str, exclude_relpath: str | None = None
) -> list[tuple[str, str]]:
    """Return (name, library-file) pairs for top-level declarations in `lean_source`
    that already exist somewhere in the engine's `PrisonersDilemma/` tree.

    Why: a proof file compiles STANDALONE even when one of its helper lemmas
    duplicates a library name in the same namespace (`PD.Theorems`) — the clash only
    surfaces at the umbrella `lake build`, AFTER the agent session ended (the
    DIMCID-vs-OBot incident: the agent's census helper reused
    `no_provable_OBot_D_tail` from `CupodBot/Helpers.lean`). Matching is by bare
    declaration name across the tree — a slight over-approximation across
    namespaces, which is fine for an advisory warning and near-exact in practice
    (all outcome files share `PD.Theorems`).

    `exclude_relpath` skips the target module itself (re-proving a pair REPLACES its
    file, so self-collisions are not clashes).
    """
    from pd_runner.config import load_paths

    names = set(_DECL_RE.findall(lean_source))
    if not names:
        return []
    root = load_paths().lean_engine_dir / "PrisonersDilemma"
    collisions: list[tuple[str, str]] = []
    for path in sorted(root.rglob("*.lean")):
        rel = path.relative_to(root).as_posix()
        if exclude_relpath is not None and rel == exclude_relpath:
            continue
        if "Research/" in rel:
            continue  # spikes are not in the build targets
        try:
            src = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for name in names & set(_DECL_RE.findall(src)):
            collisions.append((name, rel))
    return sorted(set(collisions))


_LINE_COMMENT_RE = re.compile(r"--.*$", re.MULTILINE)
_BLOCK_COMMENT_RE = re.compile(r"/-[\s\S]*?-/")
_CENSUS_INDUCTION_TOKENS = ("Pf.induct", "PlaysProof.induct", "Pf.rec", "PlaysProof.rec")


def _strip_comments(lean_source: str) -> str:
    stripped = _BLOCK_COMMENT_RE.sub("", lean_source)
    return _LINE_COMMENT_RE.sub("", stripped)


def find_census_inductions(lean_source: str) -> list[str]:
    """Return the raw `Pf`-induction tokens used in the source (comments stripped).

    Hand-rolled censuses (`induction … using Pf.induct`, or worse the raw
    recursors) in agent proof files are a maintenance hazard: they induct over
    ALL ~30 constructors, so EVERY future constructor addition breaks them with
    missing-cases. The library's exclusion architecture is two-tier for exactly
    this reason — matchup censuses must instantiate the shared kernels in
    `Base/Exclusion.lean` (`no_provable_tailTo_unreadable`,
    `no_provable_probeFirst_tail`, `no_provable_searcherPlay_tail`,
    `no_provable_tailToS_floor`), which absorb new constructors centrally.
    """
    stripped = _strip_comments(lean_source)
    return [tok for tok in _CENSUS_INDUCTION_TOKENS if tok in stripped]


def find_bot_redefinitions(lean_source: str) -> list[str]:
    """Return names of any `def X : Prog` declarations in the proof source.

    Proof files must import bots, never redefine them — a redefinition causes a
    namespace clash with `PD.Bots.X` at `lake build` time.
    """
    return _BOT_DEF_RE.findall(lean_source)


# ---------------------------------------------------------------------------
# Strict-template statement checking (the deterministic "Reviewer")
# ---------------------------------------------------------------------------

_FORBIDDEN_TOKEN_RE = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")


def expected_theorem_name(left_bot: str, right_bot: str) -> str:
    return f"llm_outcome_{left_bot}_vs_{right_bot}"


def extract_theorem_statement(lean_source: str, theorem_name: str) -> str | None:
    """The statement text of `theorem <name> ... :=` (comments stripped), or None.

    Scans from the theorem keyword to the first `:=` — good enough for the
    strict outcome-theorem template (statements never contain `:=`); the
    re-compile is the authoritative gate, this check is about SHAPE.
    """
    stripped = _strip_comments(lean_source)
    match = re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", stripped)
    if match is None:
        return None
    rest = stripped[match.end():]
    end = rest.find(":=")
    return rest[:end] if end != -1 else rest


def check_proved_source(
    lean_source: str,
    *,
    left_bot: str,
    right_bot: str,
    submitted_left: str | None,
    submitted_right: str | None,
) -> list[str]:
    """Statement-level checks for a submitted `proved` source.

    Returns a list of human-readable problems (empty = OK). Compilation is
    checked separately — these are the strict-template shape checks that
    compilation alone cannot enforce.
    """
    problems: list[str] = []

    forbidden = sorted(set(_FORBIDDEN_TOKEN_RE.findall(_strip_comments(lean_source))))
    if forbidden:
        problems.append(
            f"the source contains forbidden token(s): {', '.join(forbidden)} — "
            "proofs must be complete and axiom-free"
        )

    redefs = find_bot_redefinitions(lean_source)
    if redefs:
        problems.append(
            f"the source redefines bot(s) {', '.join(redefs)} — import the bot "
            "modules instead of redefining them"
        )

    name = expected_theorem_name(left_bot, right_bot)
    statement = extract_theorem_statement(lean_source, name)
    if statement is None:
        problems.append(
            f"no theorem named exactly `{name}` found — the final theorem must "
            "use this exact name"
        )
        return problems

    if "outcome" not in statement:
        problems.append(
            f"the statement of `{name}` does not mention `outcome` — the "
            "conclusion must be an `outcome … = …` equation"
        )

    if "proofSearch" in statement:
        problems.append(
            f"the statement of `{name}` mentions `proofSearch` — hypotheses that "
            "condition the outcome on the proof oracle are forbidden (strict "
            "theorem shape)"
        )

    parsed = extract_actions_from_source(statement)
    if parsed is None:
        problems.append(
            f"could not parse an action pair (`= some (.X, .Y)` or `= none`) "
            f"from the statement of `{name}`"
        )
        return problems

    stated_left, stated_right = parsed
    norm = lambda a: None if a in (None, "none") else a  # noqa: E731
    if (norm(submitted_left), norm(submitted_right)) != (stated_left, stated_right):
        problems.append(
            f"submitted actions ({submitted_left}, {submitted_right}) do not match "
            f"the theorem statement's actions "
            f"({stated_left or 'none'}, {stated_right or 'none'})"
        )
    return problems

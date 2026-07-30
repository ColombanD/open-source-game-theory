"""Proof-search entry points.

The real work lives in `services.proof_episodes` (the episode loop) and
`services.verdicts` (the data types + deterministic checks). This module is
the compatibility facade:

  - `search_proof_outcome(request) -> ProofOutcome` — the structured entry
    point: every terminal (proved / open_* / constructor_proposed / exhausted
    / error) is a value, never an exception.
  - `search_proof(request) -> ProofResult` — the legacy surface: returns only
    on `proved`, raises `ProofSearchError` (with `.outcome` attached) for
    everything else. Existing callers (pipeline_task, harness, matrix, CLIs)
    keep working unchanged.

The legacy names (`ProofRequest`, `ProofResult`, `ProofSearchError`, the
static source checks) are re-exported here for backward compatibility.
"""

from __future__ import annotations

from pd_runner.logging_config import get_logger

# Re-exports: the canonical definitions moved to services.verdicts.
from pd_runner.services.verdicts import (  # noqa: F401
    ProofOutcome,
    ProofRequest,
    ProofResult,
    ProofSearchError,
    extract_actions_from_source,
    find_bot_redefinitions,
    find_census_inductions,
    find_library_name_collisions,
)

# Legacy private aliases (pre-move names).
_extract_actions_from_source = extract_actions_from_source
_find_bot_redefinitions = find_bot_redefinitions

_log = get_logger("services.proof_service")


def search_proof_outcome(request: ProofRequest) -> ProofOutcome:
    """Run the episode-based proof search; every ending is a ProofOutcome.

    Infrastructure exceptions (API failures, bugs) are captured as
    kind == "error" outcomes so batch drivers never lose a record.
    """
    from pd_runner.services.proof_episodes import run_proof_search

    try:
        return run_proof_search(request)
    except Exception as exc:  # noqa: BLE001 — batch callers need a record, not a crash
        _log.exception(
            "Proof search errored for %s vs %s", request.left_bot, request.right_bot
        )
        return ProofOutcome(
            left_bot=request.left_bot,
            right_bot=request.right_bot,
            kind="error",
            explanation=f"{type(exc).__name__}: {exc}",
        )


def search_proof(request: ProofRequest) -> ProofResult:
    """Legacy surface: return a ProofResult on `proved`, raise ProofSearchError
    otherwise (with the structured `.outcome` attached)."""
    outcome = search_proof_outcome(request)

    if outcome.proved:
        return ProofResult(
            left_bot=outcome.left_bot,
            right_bot=outcome.right_bot,
            left_action=outcome.left_action,
            right_action=outcome.right_action,
            lean_source=outcome.lean_source or "",
            iterations_used=outcome.turns_used,
        )

    kind = outcome.legacy_error_kind()
    if kind == "open_constructor_proposed":
        message = (
            f"Agent declared outcome OPEN for {request.left_bot} vs {request.right_bot} "
            f"(constructor proposal '{outcome.proposal_name}' was filed under "
            "generated/constructor_proposals/ — review its faithfulness rationale; "
            f"integration is human-gated).\nAgent explanation:\n{outcome.explanation}"
        )
    elif kind in ("open_blocked", "open_bistable"):
        message = (
            f"Agent declared outcome OPEN for {request.left_bot} vs {request.right_bot} "
            f"({'blocked by a census wall' if kind == 'open_blocked' else 'bistable matchup'}).\n"
            f"Agent explanation:\n{outcome.explanation}"
        )
    elif kind == "no_output":
        message = (
            f"Agent did not produce a verdict for {request.left_bot} vs "
            f"{request.right_bot}.\n{outcome.explanation}"
        )
    else:
        message = (
            f"Proof search errored for {request.left_bot} vs {request.right_bot}: "
            f"{outcome.explanation}"
        )
    raise ProofSearchError(
        message,
        iterations_used=outcome.turns_used,
        kind=kind,
        outcome=outcome,
    )

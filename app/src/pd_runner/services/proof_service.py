"""M4: Agentic proof-search loop.

Input:  bot pair + claimed outcome
Output: proven Lean source (str) or raises ProofSearchError
"""

from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.llm.client import AnthropicClient, ToolHandler
from pd_runner.llm.prompts import build_system_prompt, proof_request_message
from pd_runner.llm.retrieval import list_known_outcome_theorems, retrieve_few_shots
from pd_runner.llm.tools import LEAN_TOOLS, register_lean_tools
from pd_runner.logging_config import get_logger, TRACE

_log = get_logger("services.proof_service")


@dataclass(frozen=True)
class ProofRequest:
    left_bot: str
    right_bot: str
    left_action: str | None = None   # None → agent must discover the outcome
    right_action: str | None = None  # None → agent must discover the outcome
    fuel: int | None = None          # None → agent must pick a suitable fuel
    max_iterations: int = 20
    max_tokens: int = 32000
    thinking_effort: str = "medium"
    model: str = "claude-opus-4-7"
    exclude_bots: frozenset[str] = frozenset()


@dataclass(frozen=True)
class ProofResult:
    left_bot: str
    right_bot: str
    left_action: str | None   # None when outcome is provably none (non-terminating)
    right_action: str | None
    lean_source: str
    iterations_used: int


class ProofSearchError(RuntimeError):
    """Raised when proof search fails. Carries iterations_used for the caller."""

    def __init__(self, message: str, *, iterations_used: int = 0) -> None:
        super().__init__(message)
        self.iterations_used = iterations_used


def _outcomes_dir() -> Path:
    """Directory where every proof attempt (pass or fail) is persisted."""
    paths = load_paths()
    d = paths.app_root / "generated" / "outcomes"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _persist_attempt(
    request: ProofRequest,
    *,
    lean_source: str | None,
    final_text: str,
    iterations: int,
    elapsed_s: float,
    passed: bool,
    left_action: str | None,
    right_action: str | None,
    error: str | None,
) -> Path:
    """Write the proof attempt and metadata sidecar for traceability."""
    ts = time.strftime("%Y%m%dT%H%M%S")
    stem = f"{request.left_bot}_vs_{request.right_bot}_{'pass' if passed else 'fail'}"
    out_dir = _outcomes_dir()
    lean_path = out_dir / f"{stem}.lean"
    meta_path = out_dir / f"{stem}.json"
    # Remove any previous outcome files for this pair (pass or fail) so only
    # the latest attempt survives.
    for old in out_dir.glob(f"{request.left_bot}_vs_{request.right_bot}_*.lean"):
        old.unlink(missing_ok=True)
    for old in out_dir.glob(f"{request.left_bot}_vs_{request.right_bot}_*.json"):
        old.unlink(missing_ok=True)
    lean_path.write_text(
        (lean_source or "-- (agent did not emit a final ```lean code block)\n") + "\n",
        encoding="utf-8",
    )
    meta = {
        "timestamp": ts,
        "bot_a": request.left_bot,
        "bot_b": request.right_bot,
        "model": request.model,
        "max_iterations": request.max_iterations,
        "max_tokens": request.max_tokens,
        "fuel_requested": request.fuel,
        "exclude_bots": sorted(request.exclude_bots),
        "passed": passed,
        "left_action": left_action,
        "right_action": right_action,
        "iterations_used": iterations,
        "elapsed_seconds": elapsed_s,
        "error": error,
        "final_text_tail": final_text[-2000:] if final_text else None,
    }
    meta_path.write_text(json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8")
    _log.info("Persisted attempt to %s", lean_path)
    return lean_path


def search_proof(request: ProofRequest) -> ProofResult:
    """Run the agentic proof-search loop for one theorem.

    Raises ProofSearchError if the agent fails to produce a verified proof.
    Every attempt (pass or fail) is persisted to `generated/outcomes/` for
    traceability — see `_persist_attempt`.
    """
    few_shots = retrieve_few_shots(request.left_bot, request.right_bot, exclude_bots=set(request.exclude_bots))
    known = list_known_outcome_theorems(request.left_bot, request.right_bot, exclude_bots=set(request.exclude_bots))

    system_prompt = build_system_prompt(request.left_bot, request.right_bot)
    user_message = proof_request_message(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=request.left_action,
        right_action=request.right_action,
        fuel=request.fuel,
        few_shot_files=few_shots,
        known_theorems_summary=known,
    )

    _log.log(TRACE, "System prompt:\n%s", system_prompt)
    _log.log(TRACE, "User message:\n%s", user_message)

    handler = ToolHandler()
    register_lean_tools(handler, exclude_bots=request.exclude_bots)

    client = AnthropicClient(
        system_prompt=system_prompt,
        tools=LEAN_TOOLS,
        model=request.model,
        max_iterations=request.max_iterations,
        max_tokens=request.max_tokens,
        thinking_effort=request.thinking_effort,
    )

    # Track how many tool calls were made by monkey-patching the handler.
    iteration_count = [0]
    original_call = handler.call

    def counting_call(tool_name: str, tool_input):
        iteration_count[0] += 1
        return original_call(tool_name, tool_input)

    handler.call = counting_call  # type: ignore[method-assign]

    t0 = time.monotonic()
    final_text = ""
    lean_source: str | None = None
    try:
        final_text = client.run(user_message, tool_handler=handler)
        lean_source = _extract_lean_source(final_text)

        if lean_source is None:
            err = (
                f"Agent did not produce a final Lean source for "
                f"{request.left_bot} vs {request.right_bot}.\n"
                f"Final response:\n{final_text}"
            )
            _persist_attempt(
                request, lean_source=None, final_text=final_text,
                iterations=iteration_count[0], elapsed_s=time.monotonic() - t0,
                passed=False, left_action=None, right_action=None, error=err,
            )
            raise ProofSearchError(err, iterations_used=iteration_count[0])

        left_action = request.left_action
        right_action = request.right_action
        if left_action is None or right_action is None:
            parsed = _extract_actions_from_source(lean_source)
            if parsed is None:
                err = (
                    f"Could not parse action pair from proven source for "
                    f"{request.left_bot} vs {request.right_bot}.\n"
                    f"Source:\n{lean_source}"
                )
                _persist_attempt(
                    request, lean_source=lean_source, final_text=final_text,
                    iterations=iteration_count[0], elapsed_s=time.monotonic() - t0,
                    passed=False, left_action=None, right_action=None, error=err,
                )
                raise ProofSearchError(err, iterations_used=iteration_count[0])
            left_action, right_action = parsed

        _persist_attempt(
            request, lean_source=lean_source, final_text=final_text,
            iterations=iteration_count[0], elapsed_s=time.monotonic() - t0,
            passed=True, left_action=left_action, right_action=right_action, error=None,
        )
        return ProofResult(
            left_bot=request.left_bot,
            right_bot=request.right_bot,
            left_action=left_action,
            right_action=right_action,
            lean_source=lean_source,
            iterations_used=iteration_count[0],
        )
    except ProofSearchError:
        raise
    except Exception as exc:
        _persist_attempt(
            request, lean_source=lean_source, final_text=final_text,
            iterations=iteration_count[0], elapsed_s=time.monotonic() - t0,
            passed=False, left_action=None, right_action=None, error=f"{type(exc).__name__}: {exc}",
        )
        raise


_NONE_OUTCOME_RE = re.compile(r"outcome\s+\w.*?=\s*none\b", re.DOTALL)


def _extract_actions_from_source(lean_source: str) -> tuple[str | None, str | None] | None:
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


def _find_bot_redefinitions(lean_source: str) -> list[str]:
    """Return names of any `def X : Prog` declarations in the proof source.

    Proof files must import bots, never redefine them — a redefinition causes a
    namespace clash with `PDNew.Bots.X` at `lake build` time.
    """
    return _BOT_DEF_RE.findall(lean_source)


def _extract_lean_source(text: str) -> str | None:
    """Pull the last ```lean ... ``` block from the agent's final response."""
    matches = re.findall(r"```lean\s*\n(.*?)```", text, re.DOTALL)
    if matches:
        return matches[-1].strip()
    return None

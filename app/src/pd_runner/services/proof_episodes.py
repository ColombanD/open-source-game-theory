"""The episode-based proof-search loop (AxProverBase-style).

Proposer → Compiler → Reviewer → Memory, adapted to this project:

  - Proposer: the LLM agent inside one episode (`AnthropicClient.run_episode`)
    with the Lean tools, the growth tools (production), `update_notebook`, and
    `submit_verdict`.
  - Compiler: `CompileService` — deterministic `lake env lean` on a temp file.
    `CompileReport.goals` is always None in v1; it is the reserved seam for
    sorry-sketch goal-state extraction (v2).
  - Reviewer: `verify_proved_submission` — DETERMINISTIC exit verification
    (re-compile the submitted source + strict-template statement check +
    census/collision hard checks). No LLM: the strict outcome-theorem template
    makes cheat-checking decidable.
  - Memory: the self-managed lab notebook (`update_notebook`, replace-whole-
    text) carried across fresh-context episodes together with the best/last
    attempt and the last compiler feedback. Hybrid trigger: voluntary during
    the episode, plus one forced reflection turn at episode end if stale.

Every episode is persisted to `generated/outcomes/` with a timestamped stem —
attempts are never deleted (longitudinal thesis data).
"""

from __future__ import annotations

import json
import time
from dataclasses import dataclass, field
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.llm.client import (
    AnthropicClient,
    EpisodeResult,
    EpisodeStop,
    ToolHandler,
    UsageTotals,
    serialize_messages,
)
from pd_runner.llm.prompts import build_system_prompt_blocks, proof_request_message
from pd_runner.llm.retrieval import list_known_outcome_theorems, retrieve_few_shots
from pd_runner.llm.tools import (
    GROWTH_TOOLS,
    LEAN_TOOLS,
    RequestContext,
    UPDATE_NOTEBOOK_TOOL,
    compile_proof_source,
    make_submit_verdict_tool,
    register_lean_tools,
)
from pd_runner.logging_config import TRACE, get_logger
from pd_runner.settings import DEFAULT_SETTINGS, AgentSettings, EvalGuard
from pd_runner.services.verdicts import (
    ProofOutcome,
    ProofRequest,
    check_proved_source,
    find_census_inductions,
    find_library_name_collisions,
)

_log = get_logger("services.proof_episodes")

_FEEDBACK_TRUNCATE_CHARS = 4_000


# ---------------------------------------------------------------------------
# Compiler (the v2 seam)
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CompileReport:
    exit_code: int
    stdout: str
    stderr: str
    # Reserved for sorry-sketch goal-state extraction (v2). Always None in v1.
    goals: list | None = None


class CompileService:
    """Deterministic compile of a candidate source against the engine."""

    def check(self, lean_source: str, *, filename_hint: str = "proof_attempt") -> CompileReport:
        result = compile_proof_source(lean_source, filename_hint)
        return CompileReport(result.returncode, result.stdout, result.stderr)


# ---------------------------------------------------------------------------
# State carried across episodes
# ---------------------------------------------------------------------------


@dataclass
class EpisodeRecord:
    index: int
    end_reason: str
    turns_used: int
    tool_calls_used: int
    usage: dict[str, int]
    notebook: str


@dataclass
class ProofState:
    notebook: str = ""
    best_attempt: str | None = None      # last source with exit code 0 from run_lean_proof
    last_attempt: str | None = None      # most recent source regardless of result
    last_feedback: str | None = None     # its compiler stderr/stdout, truncated
    episodes: list[EpisodeRecord] = field(default_factory=list)
    recorded_proposals: set[str] = field(default_factory=set)
    verification_bounces: int = 0        # failed proved-verdict verifications this episode


# ---------------------------------------------------------------------------
# Reviewer: deterministic exit verification
# ---------------------------------------------------------------------------


def verify_proved_submission(
    request: ProofRequest,
    lean_source: str,
    *,
    submitted_left: str | None,
    submitted_right: str | None,
    compile_svc: CompileService,
) -> list[str]:
    """Every reason to reject a `proved` submission (empty list = accepted).

    Mirrors the library writer's hard checks so a verdict that passes here
    also survives write time (closing the old warn-vs-refuse asymmetry).
    """
    hint = f"{request.left_bot}_vs_{request.right_bot}_verify"

    # 1. Re-compile the SUBMITTED source — never trust the last in-loop compile.
    report = compile_svc.check(lean_source, filename_hint=hint)
    if report.exit_code != 0:
        return [
            "the submitted source does not compile (exit code "
            f"{report.exit_code}):\n{(report.stderr or report.stdout)[:_FEEDBACK_TRUNCATE_CHARS]}"
        ]
    if "error" in (report.stderr or "").lower():
        return [
            f"the compiler reported errors:\n{report.stderr[:_FEEDBACK_TRUNCATE_CHARS]}"
        ]

    # 2. Strict-template statement checks (name, outcome equation, no oracle
    #    hypotheses, forbidden tokens, action match).
    problems = check_proved_source(
        lean_source,
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        submitted_left=submitted_left,
        submitted_right=submitted_right,
    )

    # 3. Hand-rolled Pf inductions — hard fail (the library writer refuses them).
    inductions = find_census_inductions(lean_source)
    if inductions:
        problems.append(
            f"the source uses hand-rolled Pf induction ({', '.join(inductions)}) — "
            "instantiate the shared exclusion kernels from Base/Exclusion.lean instead"
        )

    # 4. Library name collisions — hard fail (lake build would break at write time).
    exclude = f"Theorems/{request.left_bot}/vs_{request.right_bot}.lean"
    collisions = find_library_name_collisions(lean_source, exclude_relpath=exclude)
    if collisions:
        listing = "; ".join(f"`{n}` already in {f}" for n, f in collisions)
        problems.append(
            f"library name collisions: {listing} — rename these declarations with a "
            "matchup-specific prefix"
        )
    return problems


# ---------------------------------------------------------------------------
# Tool wiring
# ---------------------------------------------------------------------------


def _make_update_notebook(state: ProofState, cfg: AgentSettings):
    def update_notebook(notebook: str) -> str:
        text = notebook.strip()
        if len(text) > cfg.notebook_char_cap:
            text = text[: cfg.notebook_char_cap]
            state.notebook = text
            return (
                f"Notebook updated but TRUNCATED to {cfg.notebook_char_cap} characters — "
                "distill harder; drop what a fresh attempt would not need."
            )
        state.notebook = text
        return f"Notebook updated ({len(text)} characters)."

    return update_notebook


def _proposal_exists(name: str, state: ProofState) -> bool:
    """A verdict may cite a proposal filed this session OR a pending bundle on
    disk from an earlier run (the pending-proposals prompt block invites that)."""
    if name in state.recorded_proposals:
        return True
    from pd_runner.services.constructor_proposals import proposals_dir

    try:
        return (proposals_dir() / name).exists()
    except OSError:
        return False


def _make_submit_verdict(
    request: ProofRequest,
    guard: EvalGuard,
    state: ProofState,
    compile_svc: CompileService,
    cfg: AgentSettings,
):
    def submit_verdict(
        verdict: str,
        explanation: str = "",
        lean_source: str | None = None,
        left_action: str | None = None,
        right_action: str | None = None,
        proposal_name: str | None = None,
    ):
        if not explanation.strip():
            return "Verdict rejected: `explanation` is required."

        if verdict == "proved":
            if not lean_source or not lean_source.strip():
                return "Verdict rejected: `lean_source` is required for `proved`."
            if left_action is None or right_action is None:
                return (
                    "Verdict rejected: `left_action` and `right_action` are required "
                    "for `proved` ('none' for `= none` theorems)."
                )
            if state.verification_bounces >= cfg.max_verification_bounces:
                return EpisodeStop(
                    payload=None,
                    confirmation_text=(
                        "Too many failed verification attempts this episode — it ends here. "
                        "Update your notebook with what went wrong."
                    ),
                    end_reason="verification_cap",
                )
            problems = verify_proved_submission(
                request, lean_source,
                submitted_left=left_action, submitted_right=right_action,
                compile_svc=compile_svc,
            )
            if problems:
                state.verification_bounces += 1
                remaining = cfg.max_verification_bounces - state.verification_bounces
                return (
                    "Verdict rejected — fix these problems and resubmit "
                    f"({remaining} verification attempt(s) left this episode):\n- "
                    + "\n- ".join(problems)
                )
            return EpisodeStop(payload={
                "verdict": "proved",
                "lean_source": lean_source,
                "left_action": left_action,
                "right_action": right_action,
                "explanation": explanation,
            })

        if verdict == "constructor_proposed":
            if not guard.allow_library_growth:
                return (
                    "Verdict rejected: `constructor_proposed` is not available in this "
                    "session (library growth is disabled)."
                )
            if not proposal_name or not _proposal_exists(proposal_name, state):
                return (
                    "Verdict rejected: no proposal named "
                    f"{proposal_name!r} is on file — file it with "
                    "`propose_pf_constructor` first (its result must say PROPOSAL "
                    "RECORDED), or reference an existing pending proposal by its "
                    "exact name."
                )
            return EpisodeStop(payload={
                "verdict": "constructor_proposed",
                "proposal_name": proposal_name,
                "explanation": explanation,
            })

        if verdict in ("open_bistable", "open_blocked"):
            return EpisodeStop(payload={"verdict": verdict, "explanation": explanation})

        return f"Verdict rejected: unknown verdict {verdict!r}."

    return submit_verdict


def _make_tool_handler(
    request: ProofRequest,
    guard: EvalGuard,
    state: ProofState,
    compile_svc: CompileService,
    cfg: AgentSettings,
) -> ToolHandler:
    handler = ToolHandler()

    def on_attempt(lean_source: str, result) -> None:
        state.last_attempt = lean_source
        feedback = result.stderr or result.stdout or "(no compiler output)"
        state.last_feedback = feedback[:_FEEDBACK_TRUNCATE_CHARS]
        if result.returncode == 0:
            state.best_attempt = lean_source

    register_lean_tools(
        handler,
        guard=guard,
        ctx=RequestContext(request.left_bot, request.right_bot),
        on_attempt=on_attempt,
        on_proposal_recorded=state.recorded_proposals.add,
    )
    handler.register_fn("update_notebook", _make_update_notebook(state, cfg))
    handler.register_fn(
        "submit_verdict", _make_submit_verdict(request, guard, state, compile_svc, cfg)
    )
    return handler


# ---------------------------------------------------------------------------
# Episode continuation block (what a fresh context inherits)
# ---------------------------------------------------------------------------


def _episode_block(state: ProofState, episode_index: int, max_episodes: int) -> str:
    parts = [
        f"\n\n# Continuation — attempt {episode_index + 1} of {max_episodes}\n\n"
        "This is a FRESH attempt: your previous conversation was discarded. "
        "Everything you chose to keep is below. Do not repeat known dead ends."
    ]
    notebook = state.notebook.strip() or "(empty — no notes were recorded)"
    parts.append(f"## Your lab notebook (from previous attempts)\n\n{notebook}")
    if state.best_attempt:
        parts.append(
            "## Best compiling source so far (exit code 0 — may still fail the "
            "verdict checks or use a wrong statement)\n\n"
            f"```lean\n{state.best_attempt}\n```"
        )
    if state.last_attempt and state.last_attempt != state.best_attempt:
        parts.append(
            "## Most recent attempt (did not compile)\n\n"
            f"```lean\n{state.last_attempt}\n```\n\n"
            f"Compiler feedback:\n```\n{state.last_feedback or '(none)'}\n```"
        )
    return "\n\n".join(parts)


# ---------------------------------------------------------------------------
# Persistence — every episode, timestamped, never deleted
# ---------------------------------------------------------------------------


def _outcomes_dir() -> Path:
    paths = load_paths()
    d = paths.app_root / "generated" / "outcomes"
    d.mkdir(parents=True, exist_ok=True)
    return d


def _persist_episode(
    request: ProofRequest,
    state: ProofState,
    result: EpisodeResult,
    *,
    run_ts: str,
    episode_index: int,
    verdict_kind: str | None,
    elapsed_s: float,
) -> None:
    """Write one episode's artifacts. Nothing is ever deleted."""
    out_dir = _outcomes_dir()
    stem = (
        f"{request.left_bot}_vs_{request.right_bot}_{run_ts}"
        f"_ep{episode_index + 1}_{verdict_kind or result.end_reason}"
    )
    meta = {
        "timestamp": run_ts,
        "bot_a": request.left_bot,
        "bot_b": request.right_bot,
        "model": request.model,
        "episode_index": episode_index,
        "end_reason": result.end_reason,
        "verdict_kind": verdict_kind,
        "turns_used": result.turns_used,
        "tool_calls_used": result.tool_calls_used,
        "usage": result.usage.as_dict(),
        "elapsed_seconds": elapsed_s,
        "notebook": state.notebook or None,
        "hidden_bots": sorted(request.guard.hidden_bots),
        "final_text": result.final_text or None,
    }
    try:
        (out_dir / f"{stem}.json").write_text(
            json.dumps(meta, indent=2, ensure_ascii=False), encoding="utf-8"
        )
        (out_dir / f"{stem}_transcript.json").write_text(
            json.dumps(
                serialize_messages(result.messages), indent=2, ensure_ascii=False, default=str
            ),
            encoding="utf-8",
        )
        source = (
            result.verdict_input.get("lean_source")
            if result.verdict_input else None
        ) or state.best_attempt
        if source:
            (out_dir / f"{stem}.lean").write_text(source + "\n", encoding="utf-8")
        if state.notebook:
            (out_dir / f"{stem}_notebook.md").write_text(
                state.notebook + "\n", encoding="utf-8"
            )
    except OSError as exc:
        _log.warning("Could not persist episode artifacts for %s: %s", stem, exc)
    _log.info("Persisted episode %d artifacts as %s.*", episode_index + 1, stem)


# ---------------------------------------------------------------------------
# The outer loop
# ---------------------------------------------------------------------------


def _settings_for(request: ProofRequest) -> AgentSettings:
    return AgentSettings(
        model=request.model,
        max_tokens=request.max_tokens,
        thinking_effort=request.thinking_effort,
        max_turns_per_episode=request.max_iterations,
        max_episodes=(
            request.max_episodes
            if request.max_episodes is not None
            else DEFAULT_SETTINGS.max_episodes
        ),
    )


def _outcome_from_verdict(
    request: ProofRequest,
    verdict: dict,
    state: ProofState,
    totals: UsageTotals,
    turns: int,
    tool_calls: int,
) -> ProofOutcome:
    norm = lambda a: None if a in (None, "none") else a  # noqa: E731
    return ProofOutcome(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        kind=verdict["verdict"],
        lean_source=verdict.get("lean_source"),
        left_action=norm(verdict.get("left_action")),
        right_action=norm(verdict.get("right_action")),
        explanation=verdict.get("explanation", ""),
        proposal_name=verdict.get("proposal_name"),
        episodes_used=len(state.episodes),
        turns_used=turns,
        tool_calls_used=tool_calls,
        usage=totals,
        notebook=state.notebook,
    )


def run_proof_search(request: ProofRequest) -> ProofOutcome:
    """Run the full episode loop for one matchup. Never raises for agent-level
    terminals — every ending is a ProofOutcome (kind == "error" only surfaces
    via exceptions from infrastructure, handled by the caller)."""
    cfg = _settings_for(request)
    guard = request.guard
    hidden = frozenset(guard.hidden_bots)

    few_shots = retrieve_few_shots(request.left_bot, request.right_bot, exclude_bots=set(hidden))
    known = list_known_outcome_theorems(request.left_bot, request.right_bot, exclude_bots=set(hidden))
    system_blocks = build_system_prompt_blocks(
        request.left_bot, request.right_bot, guard=guard
    )
    user_prefix = proof_request_message(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        left_action=request.left_action,
        right_action=request.right_action,
        fuel=request.fuel,
        few_shot_files=few_shots,
        known_theorems_summary=known,
    )
    _log.log(TRACE, "System prompt:\n%s", "\n\n".join(system_blocks))
    _log.log(TRACE, "User message:\n%s", user_prefix)

    tools = list(LEAN_TOOLS)
    if guard.allow_library_growth:
        tools += GROWTH_TOOLS
    tools.append(make_submit_verdict_tool(guard.allow_library_growth))
    tools.append(UPDATE_NOTEBOOK_TOOL)

    client = AnthropicClient(
        system_prompt=system_blocks,
        tools=tools,
        model=cfg.model,
        max_iterations=cfg.max_turns_per_episode,
        max_tokens=cfg.max_tokens,
        thinking_effort=cfg.thinking_effort,
    )

    state = ProofState()
    compile_svc = CompileService()
    totals = UsageTotals()
    turns = 0
    tool_calls = 0
    run_ts = time.strftime("%Y%m%dT%H%M%S")
    t0 = time.monotonic()

    for ep in range(cfg.max_episodes):
        state.verification_bounces = 0
        handler = _make_tool_handler(request, guard, state, compile_svc, cfg)
        user_content = user_prefix if ep == 0 else (
            user_prefix + _episode_block(state, ep, cfg.max_episodes)
        )
        _log.info(
            "Episode %d/%d for %s vs %s starting",
            ep + 1, cfg.max_episodes, request.left_bot, request.right_bot,
        )
        result = client.run_episode(
            user_content,
            handler,
            max_turns=cfg.max_turns_per_episode,
            stop_tool="submit_verdict",
            context_token_guard=cfg.context_token_guard,
            notebook_tool="update_notebook",
        )
        totals.merge(result.usage)
        turns += result.turns_used
        tool_calls += result.tool_calls_used
        state.episodes.append(EpisodeRecord(
            index=ep,
            end_reason=result.end_reason,
            turns_used=result.turns_used,
            tool_calls_used=result.tool_calls_used,
            usage=result.usage.as_dict(),
            notebook=state.notebook,
        ))
        verdict_kind = result.verdict_input.get("verdict") if result.verdict_input else None
        _persist_episode(
            request, state, result,
            run_ts=run_ts, episode_index=ep, verdict_kind=verdict_kind,
            elapsed_s=time.monotonic() - t0,
        )
        if result.verdict_input is not None:
            return _outcome_from_verdict(
                request, result.verdict_input, state, totals, turns, tool_calls
            )
        _log.info(
            "Episode %d ended without a verdict (%s) — %s",
            ep + 1, result.end_reason,
            "starting fresh episode" if ep + 1 < cfg.max_episodes else "episodes exhausted",
        )

    explanation = (
        f"No verdict after {cfg.max_episodes} episode(s); last episode ended with "
        f"'{state.episodes[-1].end_reason if state.episodes else 'n/a'}'. "
        f"Last compiler feedback:\n{state.last_feedback or '(none)'}"
    )
    return ProofOutcome(
        left_bot=request.left_bot,
        right_bot=request.right_bot,
        kind="exhausted",
        explanation=explanation,
        episodes_used=len(state.episodes),
        turns_used=turns,
        tool_calls_used=tool_calls,
        usage=totals,
        notebook=state.notebook,
    )

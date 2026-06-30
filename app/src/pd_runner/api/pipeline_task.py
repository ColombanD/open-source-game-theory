"""Background task that runs the full bot+proof pipeline for a job."""

from __future__ import annotations

import asyncio

from pd_runner.api.jobs import Job, JobStore
from pd_runner.api.schemas import BotConflictResolution, BotDraft, JobStatus, PipelineRequest, PipelineResult
from pd_runner.config import load_paths
from pd_runner.services.bot_service import BotRequest, BotResult, search_bot
from pd_runner.services.library_writer import LibraryWriteError, write_bot_to_library, write_proof_to_library
from pd_runner.services.proof_service import ProofRequest, ProofResult, ProofSearchError, search_proof


def bot_exists(name: str) -> bool:
    paths = load_paths()
    llm_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations"
    return (llm_dir / f"{name}.lean").exists()


def bot_source_on_disk(name: str) -> str | None:
    paths = load_paths()
    for candidate in (
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / f"{name}.lean",
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{name}.lean",
    ):
        if candidate.exists():
            return candidate.read_text(encoding="utf-8")
    return None


def _resolve_bot(name: str, strategy: str | None, resolution: BotConflictResolution | None, req: PipelineRequest) -> BotResult:
    """Generate or load a bot according to the conflict resolution decision.

    The model / token / effort knobs come from the pipeline request so the bot
    writer and the proof agent run under the same user-chosen settings.
    """
    if resolution == BotConflictResolution.use_existing:
        source = bot_source_on_disk(name)
        if source is None:
            raise RuntimeError(f"Bot '{name}' not found on disk despite use_existing resolution.")
        return BotResult(bot_name=name, lean_source=source, iterations_used=0)

    if not strategy:
        raise RuntimeError(f"Bot '{name}' has no strategy description and resolution != use_existing.")
    return search_bot(BotRequest(
        bot_name=name,
        strategy_description=strategy,
        model=req.model,
        max_iterations=req.max_iterations,
        max_tokens=req.max_tokens,
        thinking_effort=req.thinking_effort,
    ))


async def run_pipeline(job: Job, req: PipelineRequest, store: JobStore) -> None:
    import logging as _logging

    loop = asyncio.get_event_loop()

    # Attach per-job log handler if a log level was requested.
    if req.log_level:
        from pd_runner.api.jobs import JobLogHandler
        level = getattr(_logging, req.log_level.upper(), _logging.INFO)
        handler = JobLogHandler(job.log_queue)
        handler.set_loop(loop)
        handler.setLevel(level)
        handler.setFormatter(_logging.Formatter("%(levelname)s %(name)s — %(message)s"))
        job.log_handler = handler
        root_logger = _logging.getLogger()
        root_logger.addHandler(handler)
        # Ensure root logger level is at least as verbose as requested.
        if root_logger.level == 0 or root_logger.level > level:
            root_logger.setLevel(level)
    # In bot-writer-only mode (no bot_b), force stop_after_bots so the pipeline
    # never tries to prove an outcome with a missing second bot.
    bots_only_mode = req.bot_b is None
    if bots_only_mode:
        job.stop_after_bots = True

    def _load_existing(name: str) -> BotResult:
        source = bot_source_on_disk(name)
        if source is None:
            raise RuntimeError(f"Bot '{name}' not found on disk (expected for prove-only mode).")
        return BotResult(bot_name=name, lean_source=source, iterations_used=0)

    def _generate_bots() -> tuple[BotResult, BotResult | None]:
        if req.prove_only:
            assert req.bot_b is not None  # prove-only requires two bots; UI enforces this
            return _load_existing(req.bot_a.name), _load_existing(req.bot_b.name)
        bot_a = _resolve_bot(req.bot_a.name, req.bot_a.strategy, req.bot_a.conflict_resolution, req)
        if req.bot_b is None:
            return bot_a, None
        bot_b = _resolve_bot(req.bot_b.name, req.bot_b.strategy, req.bot_b.conflict_resolution, req)
        return bot_a, bot_b

    def _write_bots(bot_a: BotResult, bot_b: BotResult | None) -> None:
        pairs = [(bot_a, req.bot_a)]
        if bot_b is not None and req.bot_b is not None:
            pairs.append((bot_b, req.bot_b))
        for bot, spec in pairs:
            overwrite = spec.conflict_resolution == BotConflictResolution.overwrite
            try:
                write_bot_to_library(bot, human_accept=False, dry_run=False, overwrite=overwrite)
            except LibraryWriteError as exc:
                if "already exists" not in str(exc):
                    raise

    def _prove() -> ProofResult:
        assert req.bot_b is not None  # guarded by stop_after_bots in bots-only mode
        return search_proof(ProofRequest(
            left_bot=req.bot_a.name,
            right_bot=req.bot_b.name,
            model=req.model,
            max_iterations=req.max_iterations,
            max_tokens=req.max_tokens,
            thinking_effort=req.thinking_effort,
        ))

    def _write_proof(proof: ProofResult) -> None:
        try:
            write_proof_to_library(proof, human_accept=False, dry_run=False)
        except LibraryWriteError as exc:
            if "already exists" not in str(exc):
                raise

    try:
        # --- Step 1: Generate (or load) bots ---
        job.status = JobStatus.generating_bots
        if req.prove_only:
            assert req.bot_b is not None
            job.step = f"Loading {req.bot_a.name} and {req.bot_b.name} from library..."
        elif bots_only_mode:
            job.step = f"Generating {req.bot_a.name}..."
        else:
            assert req.bot_b is not None
            job.step = f"Generating {req.bot_a.name} and {req.bot_b.name}..."
        bot_a, bot_b = await loop.run_in_executor(None, _generate_bots)

        # --- Gate 1: Pause for human to review and accept bots ---
        job.status = JobStatus.bots_ready
        job.step = None
        job.bot_a_draft = bot_a
        job.bot_b_draft = bot_b
        await job.bots_accepted.wait()

        if job.rejected:
            job.status = JobStatus.failed
            job.error = "Rejected by user."
            return

        # --- Step 2: Write bots to library (skipped in prove-only mode — bots already exist) ---
        job.status = JobStatus.proving
        if not req.prove_only:
            job.step = "Writing bots to library..."
            await loop.run_in_executor(None, lambda: _write_bots(bot_a, bot_b))

        # If the user asked to stop after accepting the bots, finalise now and skip proof.
        if job.stop_after_bots:
            job.status = JobStatus.done
            job.step = None
            job.result = PipelineResult(
                bot_a_name=req.bot_a.name,
                bot_a_source=bot_a.lean_source,
                bot_b_name=(req.bot_b.name if req.bot_b is not None else None),
                bot_b_source=(bot_b.lean_source if bot_b is not None else None),
                left_action=None,
                right_action=None,
                proof_source=None,
            )
            return

        # --- Step 3: Prove outcome ---
        assert req.bot_b is not None  # bots_only_mode would have returned above
        job.step = f"Proving outcome: {req.bot_a.name} vs {req.bot_b.name}..."
        proof = await loop.run_in_executor(None, _prove)

        # --- Gate 2: Pause for human to review and accept proof ---
        job.status = JobStatus.proof_ready
        job.step = None
        job.proof_draft = proof
        await job.proof_accepted.wait()

        if job.rejected:
            job.status = JobStatus.failed
            job.error = "Proof rejected by user."
            return

        # --- Step 4: Write proof to library ---
        job.step = "Writing proof to library..."
        await loop.run_in_executor(None, lambda: _write_proof(proof))

        job.status = JobStatus.done
        job.step = None
        assert req.bot_b is not None and bot_b is not None  # full-pipeline path
        job.result = PipelineResult(
            bot_a_name=req.bot_a.name,
            bot_a_source=bot_a.lean_source,
            bot_b_name=req.bot_b.name,
            bot_b_source=bot_b.lean_source,
            left_action=proof.left_action,
            right_action=proof.right_action,
            proof_source=proof.lean_source,
        )

    except Exception as exc:
        job.status = JobStatus.failed
        job.step = None
        job.error = str(exc)
    finally:
        if job.log_handler is not None:
            import logging as _logging
            _logging.getLogger().removeHandler(job.log_handler)
        job.logs_done = True

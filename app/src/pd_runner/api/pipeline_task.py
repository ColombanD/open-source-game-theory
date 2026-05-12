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


def _resolve_bot(name: str, strategy: str, resolution: BotConflictResolution | None, model: str, max_iterations: int) -> BotResult:
    """Generate or load a bot according to the conflict resolution decision."""
    if resolution == BotConflictResolution.use_existing:
        source = bot_source_on_disk(name)
        if source is None:
            raise RuntimeError(f"Bot '{name}' not found on disk despite use_existing resolution.")
        return BotResult(bot_name=name, lean_source=source, iterations_used=0)

    return search_bot(BotRequest(
        bot_name=name,
        strategy_description=strategy,
        model=model,
        max_iterations=max_iterations,
    ))


async def run_pipeline(job: Job, req: PipelineRequest, store: JobStore) -> None:
    loop = asyncio.get_event_loop()

    def _generate_bots() -> tuple[BotResult, BotResult]:
        bot_a = _resolve_bot(req.bot_a.name, req.bot_a.strategy, req.bot_a.conflict_resolution, req.model, req.max_iterations)
        bot_b = _resolve_bot(req.bot_b.name, req.bot_b.strategy, req.bot_b.conflict_resolution, req.model, req.max_iterations)
        return bot_a, bot_b

    def _write_bots(bot_a: BotResult, bot_b: BotResult) -> None:
        for bot, spec in ((bot_a, req.bot_a), (bot_b, req.bot_b)):
            overwrite = spec.conflict_resolution == BotConflictResolution.overwrite
            try:
                write_bot_to_library(bot, human_accept=False, dry_run=False, overwrite=overwrite)
            except LibraryWriteError as exc:
                if "already exists" not in str(exc):
                    raise

    def _prove() -> ProofResult:
        return search_proof(ProofRequest(
            left_bot=req.bot_a.name,
            right_bot=req.bot_b.name,
            model=req.model,
            max_iterations=req.max_iterations,
        ))

    def _write_proof(proof: ProofResult) -> None:
        try:
            write_proof_to_library(proof, human_accept=False, dry_run=False)
        except LibraryWriteError as exc:
            if "already exists" not in str(exc):
                raise

    try:
        # --- Step 1: Generate both bots ---
        job.status = JobStatus.generating_bots
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

        # --- Step 2: Write bots to library ---
        job.status = JobStatus.proving
        job.step = "Writing bots to library..."
        await loop.run_in_executor(None, lambda: _write_bots(bot_a, bot_b))

        # --- Step 3: Prove outcome ---
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

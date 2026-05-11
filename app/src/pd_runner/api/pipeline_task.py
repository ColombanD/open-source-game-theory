"""Background task that runs the full bot+proof pipeline for a job."""

from __future__ import annotations

import asyncio
from pathlib import Path

from pd_runner.api.jobs import Job, JobStore
from pd_runner.api.schemas import JobStatus, PipelineRequest, PipelineResult
from pd_runner.config import load_paths
from pd_runner.services.bot_service import BotRequest, BotResult, BotWriteError, search_bot
from pd_runner.services.library_writer import LibraryWriteError, write_bot_to_library, write_proof_to_library
from pd_runner.services.proof_service import ProofRequest, ProofResult, ProofSearchError, search_proof


def _bot_source_on_disk(bot_name: str) -> str | None:
    paths = load_paths()
    for candidate in (
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / f"{bot_name}.lean",
        paths.lean_engine_dir / "PrisonersDilemma" / "Bots" / "LlmGenerations" / f"{bot_name}.lean",
    ):
        if candidate.exists():
            return candidate.read_text(encoding="utf-8")
    return None


async def run_pipeline(job: Job, req: PipelineRequest, store: JobStore) -> None:
    loop = asyncio.get_event_loop()

    def _generate_bots() -> tuple[BotResult, BotResult]:
        """Generate both bots (or load from disk). Returns (bot_a, bot_b)."""
        def _get(name: str, strategy: str) -> BotResult:
            existing = _bot_source_on_disk(name)
            if existing:
                return BotResult(bot_name=name, lean_source=existing, iterations_used=0)
            return search_bot(BotRequest(
                bot_name=name,
                strategy_description=strategy,
                model=req.model,
                max_iterations=req.max_iterations,
            ))

        bot_a = _get(req.bot_a_name, req.bot_a_strategy)
        bot_b = _get(req.bot_b_name, req.bot_b_strategy)
        return bot_a, bot_b

    def _write_bots(bot_a: BotResult, bot_b: BotResult) -> None:
        for bot in (bot_a, bot_b):
            try:
                write_bot_to_library(bot, human_accept=False, dry_run=False)
            except LibraryWriteError as exc:
                if "already exists" not in str(exc):
                    raise

    def _prove() -> ProofResult:
        return search_proof(ProofRequest(
            left_bot=req.bot_a_name,
            right_bot=req.bot_b_name,
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
        job.step = f"Generating {req.bot_a_name} and {req.bot_b_name}..."
        bot_a, bot_b = await loop.run_in_executor(None, _generate_bots)

        # --- Gate 1: Pause and wait for human to accept bots ---
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
        job.step = f"Proving outcome: {req.bot_a_name} vs {req.bot_b_name}..."
        proof = await loop.run_in_executor(None, _prove)

        # --- Gate 2: Pause and wait for human to accept proof ---
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
            bot_a_name=req.bot_a_name,
            bot_a_source=bot_a.lean_source,
            bot_b_name=req.bot_b_name,
            bot_b_source=bot_b.lean_source,
            left_action=proof.left_action,
            right_action=proof.right_action,
            proof_source=proof.lean_source,
        )

    except Exception as exc:
        job.status = JobStatus.failed
        job.step = None
        job.error = str(exc)

"""In-memory job store for async pipeline runs."""

from __future__ import annotations

import asyncio
import uuid
from dataclasses import dataclass, field
from typing import Optional

from pd_runner.api.schemas import BotDraft, JobStatus, PipelineResult, ProofDraft
from pd_runner.services.bot_service import BotResult
from pd_runner.services.proof_service import ProofResult


@dataclass
class Job:
    job_id: str
    status: JobStatus = JobStatus.pending
    step: Optional[str] = None

    # Drafts waiting for human acceptance
    bot_a_draft: Optional[BotResult] = None
    bot_b_draft: Optional[BotResult] = None
    proof_draft: Optional[ProofResult] = None

    # Human decision signals (set by accept/reject endpoints)
    bots_accepted: asyncio.Event = field(default_factory=asyncio.Event)
    proof_accepted: asyncio.Event = field(default_factory=asyncio.Event)
    rejected: bool = False  # True if user rejected at either gate
    stop_after_bots: bool = False  # True if user accepted bots but wants to skip the proof step

    result: Optional[PipelineResult] = None
    error: Optional[str] = None

    def to_response_dict(self) -> dict:
        """Serialisable snapshot for JobResponse."""
        bot_a = None
        if self.bot_a_draft:
            bot_a = BotDraft(name=self.bot_a_draft.bot_name, source=self.bot_a_draft.lean_source,
                             is_existing=self.bot_a_draft.iterations_used == 0)
        bot_b = None
        if self.bot_b_draft:
            bot_b = BotDraft(name=self.bot_b_draft.bot_name, source=self.bot_b_draft.lean_source,
                             is_existing=self.bot_b_draft.iterations_used == 0)
        proof = None
        if self.proof_draft:
            proof = ProofDraft(
                left_action=self.proof_draft.left_action,
                right_action=self.proof_draft.right_action,
                source=self.proof_draft.lean_source,
            )
        return {
            "job_id": self.job_id,
            "status": self.status,
            "step": self.step,
            "bot_a": bot_a,
            "bot_b": bot_b,
            "proof": proof,
            "result": self.result,
            "error": self.error,
        }


class JobStore:
    def __init__(self) -> None:
        self._jobs: dict[str, Job] = {}

    def create(self) -> Job:
        job = Job(job_id=str(uuid.uuid4()))
        self._jobs[job.job_id] = job
        return job

    def get(self, job_id: str) -> Optional[Job]:
        return self._jobs.get(job_id)


# Module-level singleton shared across requests.
store = JobStore()

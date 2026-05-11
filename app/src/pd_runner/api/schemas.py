from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import BaseModel


class PipelineRequest(BaseModel):
    bot_a_name: str
    bot_a_strategy: str
    bot_b_name: str
    bot_b_strategy: str
    model: str = "claude-sonnet-4-6"
    max_iterations: int = 20


class JobStatus(str, Enum):
    pending = "pending"
    generating_bots = "generating_bots"
    bots_ready = "bots_ready"       # waiting for human to accept bots
    proving = "proving"
    proof_ready = "proof_ready"     # waiting for human to accept proof
    done = "done"
    failed = "failed"


class BotDraft(BaseModel):
    name: str
    source: str


class ProofDraft(BaseModel):
    left_action: str
    right_action: str
    source: str


class PipelineResult(BaseModel):
    bot_a_name: str
    bot_a_source: str
    bot_b_name: str
    bot_b_source: str
    left_action: str
    right_action: str
    proof_source: str


class JobResponse(BaseModel):
    job_id: str
    status: JobStatus
    step: Optional[str] = None
    # Populated at bots_ready — shown to user for acceptance
    bot_a: Optional[BotDraft] = None
    bot_b: Optional[BotDraft] = None
    # Populated at proof_ready — shown to user for acceptance
    proof: Optional[ProofDraft] = None
    # Populated at done
    result: Optional[PipelineResult] = None
    error: Optional[str] = None

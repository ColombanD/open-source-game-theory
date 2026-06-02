from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import BaseModel


class BotConflictResolution(str, Enum):
    overwrite = "overwrite"      # regenerate and overwrite existing
    use_existing = "use_existing"  # skip generation, use the file on disk
    # rename: client just changes bot_a_name / bot_b_name to a new value


class BotSpec(BaseModel):
    name: str
    strategy: str
    conflict_resolution: Optional[BotConflictResolution] = None


class PipelineRequest(BaseModel):
    bot_a: BotSpec
    # bot_b is optional: when None, the pipeline runs in "bot writer only" mode and
    # skips the proof step entirely. Only bot_a is generated and written to the library.
    bot_b: Optional[BotSpec] = None
    model: str = "claude-sonnet-4-6"
    max_iterations: int = 20


class BotConflict(BaseModel):
    name: str
    existing_source: str


class ConflictResponse(BaseModel):
    conflicts: list[BotConflict]


class JobStatus(str, Enum):
    pending = "pending"
    generating_bots = "generating_bots"
    bots_ready = "bots_ready"
    proving = "proving"
    proof_ready = "proof_ready"
    done = "done"
    failed = "failed"


class BotDraft(BaseModel):
    name: str
    source: str
    is_existing: bool = False   # True if loaded from disk rather than generated


class ProofDraft(BaseModel):
    left_action: str
    right_action: str
    source: str


class PipelineResult(BaseModel):
    bot_a_name: str
    bot_a_source: str
    # bot_b fields are None in bot-writer-only mode (no second bot submitted).
    bot_b_name: Optional[str] = None
    bot_b_source: Optional[str] = None
    # Proof fields are None when the user chose to save bots and skip the proof step.
    left_action: Optional[str] = None
    right_action: Optional[str] = None
    proof_source: Optional[str] = None


class JobResponse(BaseModel):
    job_id: str
    status: JobStatus
    step: Optional[str] = None
    bot_a: Optional[BotDraft] = None
    bot_b: Optional[BotDraft] = None
    proof: Optional[ProofDraft] = None
    result: Optional[PipelineResult] = None
    error: Optional[str] = None

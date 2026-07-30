from __future__ import annotations

from enum import Enum
from typing import Optional

from pydantic import BaseModel, field_validator, model_validator


class BotConflictResolution(str, Enum):
    overwrite = "overwrite"      # regenerate and overwrite existing
    use_existing = "use_existing"  # skip generation, use the file on disk
    # rename: client just changes bot_a_name / bot_b_name to a new value


class BotSpec(BaseModel):
    name: str
    # strategy is optional: only required for bot-writer flows. In "prove existing bots"
    # mode the bot is loaded from disk by name and no NL description is needed.
    strategy: Optional[str] = None
    conflict_resolution: Optional[BotConflictResolution] = None


# Claude models the UI offers, with their max output-token ceilings. The agent
# spends `max_tokens` on thinking + the final answer combined, so the cap must
# stay within the chosen model's ceiling. Keep this in sync with the UI dropdown.
ALLOWED_MODELS: dict[str, int] = {
    "claude-opus-4-7": 128000,
    "claude-opus-4-8": 128000,
    "claude-sonnet-4-6": 64000,
    "claude-haiku-4-5": 64000,
}
# "none" disables extended thinking entirely — the reliable choice for models
# that only support adaptive thinking (claude-opus-4-8), which can go silent
# for minutes on hard proof turns.
ALLOWED_THINKING_EFFORTS = ("none", "low", "medium", "high")


class PipelineRequest(BaseModel):
    bot_a: BotSpec
    # bot_b is optional: when None, the pipeline runs in "bot writer only" mode and
    # skips the proof step entirely. Only bot_a is generated and written to the library.
    bot_b: Optional[BotSpec] = None
    model: str = "claude-sonnet-4-6"
    max_iterations: int = 20
    # Per-API-call output budget (thinking + answer share it). Capped to the
    # chosen model's ceiling by the validator below.
    max_tokens: int = 32000
    # Thinking depth: "none" | "low" | "medium" | "high" ("none" = no thinking).
    thinking_effort: str = "medium"
    # Prove-only mode: skip bot generation entirely; both bot_a and bot_b must already
    # exist on disk (in Bots/ or Bots/LlmGenerations/). strategy fields are ignored.
    prove_only: bool = False
    # Log level for streaming: "DEBUG", "INFO", "WARNING". None = no streaming.
    log_level: Optional[str] = None

    @field_validator("model")
    @classmethod
    def _check_model(cls, v: str) -> str:
        if v not in ALLOWED_MODELS:
            raise ValueError(f"model must be one of {sorted(ALLOWED_MODELS)}, got {v!r}")
        return v

    @field_validator("thinking_effort")
    @classmethod
    def _check_effort(cls, v: str) -> str:
        if v not in ALLOWED_THINKING_EFFORTS:
            raise ValueError(f"thinking_effort must be one of {ALLOWED_THINKING_EFFORTS}, got {v!r}")
        return v

    @model_validator(mode="after")
    def _clamp_max_tokens(self) -> "PipelineRequest":
        ceiling = ALLOWED_MODELS[self.model]
        if self.max_tokens < 1024:
            raise ValueError("max_tokens must be at least 1024")
        if self.max_tokens > ceiling:
            object.__setattr__(self, "max_tokens", ceiling)
        return self


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
    # Constructor-integration jobs (Stage C/D of an accepted proposal)
    integrating = "integrating"      # agent working in the worktree
    diff_ready = "diff_ready"        # human gate 2: review the engine diff
    applying = "applying"            # applying the accepted patch + live rebuild


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
    status_note: Optional[str] = None
    open_suggestion: Optional[dict] = None
    # Constructor-integration jobs only
    proposal_name: Optional[str] = None
    diff: Optional[str] = None
    integration_summary: Optional[str] = None


class MatrixStatusRequest(BaseModel):
    """Curated-status entry to append to outcome_status.toml."""
    section: str          # "open" | "tried" | "rework"
    pair: list[str]       # two library bot names, order-insensitive
    reason: str = ""


class ProposalInfo(BaseModel):
    name: str
    date: Optional[str] = None
    status: str = "awaiting_review"       # awaiting_review | integrated
    integrated_as: Optional[str] = None   # live constructor name once integrated
    unblocks: Optional[str] = None
    has_unblocked_proof: bool = False
    proposal_md: Optional[str] = None


class ProposalsResponse(BaseModel):
    proposals: list[ProposalInfo]


class IntegrationRequest(BaseModel):
    model: str = "claude-opus-4-7"
    max_iterations: int = 60
    max_tokens: int = 32000
    thinking_effort: str = "medium"
    log_level: Optional[str] = None

    @field_validator("model")
    @classmethod
    def _check_model(cls, v: str) -> str:
        if v not in ALLOWED_MODELS:
            raise ValueError(f"model must be one of {sorted(ALLOWED_MODELS)}, got {v!r}")
        return v

    @field_validator("thinking_effort")
    @classmethod
    def _check_effort(cls, v: str) -> str:
        if v not in ALLOWED_THINKING_EFFORTS:
            raise ValueError(f"thinking_effort must be one of {ALLOWED_THINKING_EFFORTS}, got {v!r}")
        return v

"""FastAPI application for the open-source game theory pipeline."""

from __future__ import annotations

from pathlib import Path

from fastapi import BackgroundTasks, FastAPI, HTTPException
from fastapi.responses import HTMLResponse
from fastapi.staticfiles import StaticFiles

from pd_runner.api.jobs import store
from pd_runner.api.pipeline_task import bot_exists, bot_source_on_disk, run_pipeline
from pd_runner.api.schemas import (
    BotConflict, BotConflictResolution, BotSpec,
    ConflictResponse, JobResponse, JobStatus, PipelineRequest,
)

app = FastAPI(title="Open-Source Game Theory Pipeline", version="0.1.0")

_STATIC_DIR = Path(__file__).parent / "static"
_STATIC_DIR.mkdir(exist_ok=True)
app.mount("/static", StaticFiles(directory=_STATIC_DIR), name="static")


@app.get("/", response_class=HTMLResponse)
async def index() -> HTMLResponse:
    return HTMLResponse((_STATIC_DIR / "index.html").read_text(encoding="utf-8"))


def _unresolved_conflicts(req: PipelineRequest) -> list[BotConflict]:
    """Return conflicts for bots that already exist and have no resolution set."""
    conflicts = []
    specs = [req.bot_a] + ([req.bot_b] if req.bot_b is not None else [])
    for spec in specs:
        if bot_exists(spec.name) and spec.conflict_resolution is None:
            source = bot_source_on_disk(spec.name) or ""
            conflicts.append(BotConflict(name=spec.name, existing_source=source))
    return conflicts


@app.post("/pipeline", response_model=JobResponse, status_code=202,
          responses={409: {"model": ConflictResponse}})
async def start_pipeline(req: PipelineRequest, background_tasks: BackgroundTasks):
    conflicts = _unresolved_conflicts(req)
    if conflicts:
        raise HTTPException(status_code=409, detail=ConflictResponse(conflicts=conflicts).model_dump())

    job = store.create()
    background_tasks.add_task(run_pipeline, job, req, store)
    return JobResponse(**job.to_response_dict())


@app.get("/pipeline/{job_id}", response_model=JobResponse)
async def get_job(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    return JobResponse(**job.to_response_dict())


@app.post("/pipeline/{job_id}/accept-bots", response_model=JobResponse)
async def accept_bots(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.bots_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for bot acceptance (status: {job.status})")
    job.bots_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.post("/pipeline/{job_id}/accept-bots-stop", response_model=JobResponse)
async def accept_bots_stop(job_id: str) -> JobResponse:
    """Accept the generated bots, write them to the library, and skip the proof step."""
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.bots_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for bot acceptance (status: {job.status})")
    job.stop_after_bots = True
    job.bots_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.post("/pipeline/{job_id}/reject-bots", response_model=JobResponse)
async def reject_bots(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.bots_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for bot acceptance (status: {job.status})")
    job.rejected = True
    job.bots_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.post("/pipeline/{job_id}/accept-proof", response_model=JobResponse)
async def accept_proof(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.proof_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for proof acceptance (status: {job.status})")
    job.proof_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.post("/pipeline/{job_id}/reject-proof", response_model=JobResponse)
async def reject_proof(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.proof_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for proof acceptance (status: {job.status})")
    job.rejected = True
    job.proof_accepted.set()
    return JobResponse(**job.to_response_dict())


def create_app() -> FastAPI:
    return app

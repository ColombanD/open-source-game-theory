"""FastAPI application for the open-source game theory pipeline."""

from __future__ import annotations

from pathlib import Path

import asyncio

from fastapi import BackgroundTasks, FastAPI, HTTPException
from fastapi.responses import HTMLResponse, StreamingResponse
from fastapi.staticfiles import StaticFiles

from pd_runner.api.integration_task import run_integration
from pd_runner.api.jobs import store
from pd_runner.api.pipeline_task import bot_exists, bot_source_on_disk, run_pipeline
from pd_runner.api.schemas import (
    BotConflict, BotConflictResolution, BotSpec,
    ConflictResponse, IntegrationRequest, JobResponse, JobStatus,
    PipelineRequest, ProposalInfo, ProposalsResponse,
)

app = FastAPI(title="Open-Source Game Theory Pipeline", version="0.1.0")

_STATIC_DIR = Path(__file__).parent / "static"
_STATIC_DIR.mkdir(exist_ok=True)
app.mount("/static", StaticFiles(directory=_STATIC_DIR), name="static")


@app.get("/", response_class=HTMLResponse)
async def index() -> HTMLResponse:
    return HTMLResponse((_STATIC_DIR / "index.html").read_text(encoding="utf-8"))


def _unresolved_conflicts(req: PipelineRequest) -> list[BotConflict]:
    """Return conflicts for bots that already exist and have no resolution set.

    In prove-only mode there are no conflicts to surface — both bots are expected
    to already exist on disk and are loaded as-is.
    """
    if req.prove_only:
        return []
    conflicts = []
    specs = [req.bot_a] + ([req.bot_b] if req.bot_b is not None else [])
    for spec in specs:
        if bot_exists(spec.name) and spec.conflict_resolution is None:
            source = bot_source_on_disk(spec.name) or ""
            conflicts.append(BotConflict(name=spec.name, existing_source=source))
    return conflicts


@app.get("/bots")
async def list_bots() -> dict:
    """List bot names available on disk under Bots/ and Bots/LlmGenerations/."""
    from pd_runner.config import load_paths
    paths = load_paths()
    bots_dir = paths.lean_engine_dir / "PrisonersDilemma" / "Bots"
    handwritten = sorted(p.stem for p in bots_dir.glob("*.lean"))
    llm_dir = bots_dir / "LlmGenerations"
    llm = sorted(p.stem for p in llm_dir.glob("*.lean")) if llm_dir.exists() else []
    return {"handwritten": handwritten, "llm": llm}


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


@app.get("/proposals", response_model=ProposalsResponse)
async def list_proposals() -> ProposalsResponse:
    """List filed constructor proposals (Tier-2 evidence bundles) with status."""
    import json
    from pd_runner.services.constructor_proposals import proposals_dir

    out: list[ProposalInfo] = []
    root = proposals_dir()
    if root.exists():
        for meta_path in sorted(root.glob("*/meta.json")):
            try:
                meta = json.loads(meta_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            md_path = meta_path.parent / "proposal.md"
            out.append(ProposalInfo(
                name=meta.get("name", meta_path.parent.name),
                date=meta.get("date"),
                status=meta.get("status", "awaiting_review"),
                unblocks=meta.get("unblocks"),
                has_unblocked_proof=meta.get("has_unblocked_proof", False),
                proposal_md=md_path.read_text(encoding="utf-8") if md_path.exists() else None,
            ))
    return ProposalsResponse(proposals=out)


@app.post("/proposals/{name}/integrate", response_model=JobResponse, status_code=202)
async def start_integration(name: str, req: IntegrationRequest, background_tasks: BackgroundTasks):
    """Human gate 1: accepting the constructor = starting its integration job."""
    from pd_runner.services.constructor_proposals import proposals_dir

    pdir = proposals_dir() / name
    if not pdir.exists():
        raise HTTPException(status_code=404, detail=f"No proposal named {name!r}")
    import json
    try:
        meta = json.loads((pdir / "meta.json").read_text(encoding="utf-8"))
        if meta.get("status") == "integrated":
            raise HTTPException(status_code=409, detail=f"Proposal {name!r} is already integrated")
    except (OSError, json.JSONDecodeError):
        pass

    job = store.create()
    background_tasks.add_task(run_integration, job, name, req, store)
    return JobResponse(**job.to_response_dict())


@app.post("/integration/{job_id}/accept-diff", response_model=JobResponse)
async def accept_diff(job_id: str) -> JobResponse:
    """Human gate 2: accept the reviewed engine diff — applies it to the live tree."""
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.diff_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for diff review (status: {job.status})")
    job.diff_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.post("/integration/{job_id}/reject-diff", response_model=JobResponse)
async def reject_diff(job_id: str) -> JobResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")
    if job.status != JobStatus.diff_ready:
        raise HTTPException(status_code=409, detail=f"Job is not waiting for diff review (status: {job.status})")
    job.rejected = True
    job.diff_accepted.set()
    return JobResponse(**job.to_response_dict())


@app.get("/pipeline/{job_id}/logs")
async def stream_logs(job_id: str) -> StreamingResponse:
    job = store.get(job_id)
    if job is None:
        raise HTTPException(status_code=404, detail="Job not found")

    async def _generate():
        # Open the stream immediately so the browser's EventSource connects and
        # starts rendering before the first real log record arrives.
        yield ": connected\n\n"
        while True:
            # Drain anything already queued before blocking, then close promptly
            # once the pipeline has signalled completion.
            if job.logs_done and job.log_queue.empty():
                yield "event: done\ndata: \n\n"
                break
            try:
                # Block until a record is available (with a timeout so we can
                # still notice logs_done and emit periodic heartbeats). Awaiting
                # here yields control back to the event loop after every single
                # record, which forces uvicorn to flush each SSE event instead
                # of coalescing a burst of back-to-back yields into one write.
                line = await asyncio.wait_for(job.log_queue.get(), timeout=10.0)
                # SSE is line-oriented: every line of a multi-line record needs
                # its own `data: ` prefix (EventSource rejoins them with \n).
                # Embedding raw newlines in one data field makes the browser
                # parse the continuation lines as SSE fields and drop them —
                # which used to eat everything after the first line of Lean
                # sources, tool results, and assistant text.
                payload = "".join(f"data: {l}\n" for l in (line.splitlines() or [""]))
                yield payload + "\n"
            except asyncio.TimeoutError:
                if job.logs_done and job.log_queue.empty():
                    yield "event: done\ndata: \n\n"
                    break
                # Heartbeat keeps the connection from being idle-closed during
                # long quiet stretches (e.g. a slow LLM/Lean call).
                yield ": keepalive\n\n"

    return StreamingResponse(_generate(), media_type="text/event-stream",
                             headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


def create_app() -> FastAPI:
    return app

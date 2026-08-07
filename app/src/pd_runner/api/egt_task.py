"""Background task that runs an EGT `(t, α)` sweep for a job.

Flow: sweeping → done. There are no human gates: the sweep only reads the
proven outcome matrix and writes analysis artefacts under `generated/egt/`,
so nothing lands in the library and nothing needs accepting.

Progress reaches the browser through the same SSE channel as the other jobs.
The sweep driver takes an `on_event` callback rather than logging, so this
module bridges it into `job.log_queue` directly — the callback fires from a
worker thread, hence `call_soon_threadsafe`.
"""

from __future__ import annotations

import asyncio

from pd_runner.api.jobs import Job
from pd_runner.api.schemas import EgtSweepRequest, JobStatus
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT, sweep
from pd_runner.tau.matrix import get_zoo


def _resolve_alphas(req: EgtSweepRequest):
    """`None` (defaults) | 'phases' | an explicit list."""
    if req.alphas is None:
        return None
    raw = req.alphas.strip()
    if not raw:
        return None
    if raw == "phases":
        return "phases"
    try:
        return [float(x) for x in raw.split(",") if x.strip()]
    except ValueError as exc:
        raise ValueError(
            f"alphas must be comma-separated numbers or 'phases', got {req.alphas!r}"
        ) from exc


def _resolve_ts(req: EgtSweepRequest):
    if not req.ts:
        return None
    try:
        return [float(x) for x in req.ts.split(",") if x.strip()]
    except ValueError as exc:
        raise ValueError(
            f"ts must be comma-separated numbers, got {req.ts!r}"
        ) from exc


async def run_egt_sweep(job: Job, req: EgtSweepRequest) -> None:
    loop = asyncio.get_event_loop()

    def emit(message: str) -> None:
        # Called from the executor thread; hop back onto the loop to enqueue.
        if not loop.is_closed():
            loop.call_soon_threadsafe(job.log_queue.put_nowait, message)

    try:
        # Validate before claiming the job is running, so a typo fails fast
        # with a useful message instead of dying mid-sweep.
        zoo = get_zoo(req.zoo)
        alphas = _resolve_alphas(req)
        ts = _resolve_ts(req)
        stages = tuple(s.strip() for s in req.stages.split(",") if s.strip())
        if not stages:
            raise ValueError("at least one stage must be selected")

        job.status = JobStatus.sweeping
        job.step = f"Running the EGT sweep over the {zoo.label} zoo..."
        emit(f"zoo: {zoo.label} ({len(zoo.bots)} bots)")
        if zoo.stipulations:
            emit(
                f"NOTE: {len(zoo.stipulations)} stipulated cell(s) — every result "
                "over this zoo is conditional on them."
            )
        emit(f"stages: {', '.join(stages)}")

        result = await loop.run_in_executor(None, lambda: sweep(
            zoo=req.zoo,
            ts=ts,
            alphas=alphas,
            out_root=DEFAULT_OUT_ROOT,
            stages=stages,
            t_steps=req.t_steps,
            max_support_size=req.max_support_size,
            render=req.render,
            on_event=emit,
        ))

        job.egt_result = result.summary()
        job.status = JobStatus.done if result.ok else JobStatus.failed
        job.step = None
        if not result.ok:
            failed = [r.paths.name for r in result.runs if not r.ok]
            job.error = (
                f"{len(failed)} of {result.n_distinct} analysed matrices had a "
                f"failing stage: {', '.join(failed[:3])}"
                + (" …" if len(failed) > 3 else "")
            )

    except (KeyError, ValueError) as exc:
        # KeyError: unknown zoo (get_zoo lists the valid keys in its message).
        job.status = JobStatus.failed
        job.step = None
        job.error = str(exc).strip("'")
    except Exception as exc:  # pragma: no cover — surface anything unexpected
        job.status = JobStatus.failed
        job.step = None
        job.error = f"{type(exc).__name__}: {exc}"
    finally:
        job.logs_done = True

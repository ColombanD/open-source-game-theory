"""Background task that runs a constructor-integration job (Stage C/D).

Flow: integrating (agent in worktree) → diff_ready (human gate 2) →
applying (patch + live rebuild) → done. Rejection at the gate discards the
worktree; every failure path cleans up after itself.
"""

from __future__ import annotations

import asyncio

from pd_runner.api.jobs import Job, JobStore
from pd_runner.api.schemas import IntegrationRequest, JobStatus
from pd_runner.services.constructor_integration import (
    IntegrationError,
    apply_integration,
    discard_integration,
    integrate_constructor,
)


async def run_integration(job: Job, proposal_name: str, req: IntegrationRequest, store: JobStore) -> None:
    import logging as _logging

    loop = asyncio.get_event_loop()
    job.proposal_name = proposal_name

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
        if root_logger.level == 0 or root_logger.level > level:
            root_logger.setLevel(level)

    try:
        # --- Stage C: agent integrates in an isolated worktree ---
        job.status = JobStatus.integrating
        job.step = f"Integrating `{proposal_name}` in a worktree (both lake targets must go green)..."
        result = await loop.run_in_executor(None, lambda: integrate_constructor(
            proposal_name,
            model=req.model,
            max_iterations=req.max_iterations,
            max_tokens=req.max_tokens,
            thinking_effort=req.thinking_effort,
        ))

        # --- Human gate 2: review the engine diff ---
        job.status = JobStatus.diff_ready
        job.step = None
        job.diff = result.diff
        job.integration_summary = result.summary
        job.integration_result = result
        await job.diff_accepted.wait()

        if job.rejected:
            await loop.run_in_executor(None, lambda: discard_integration(result))
            job.status = JobStatus.failed
            job.error = "Engine diff rejected by user (worktree discarded; transcript kept)."
            return

        # --- Stage D: apply to the live tree, rebuild, mark integrated ---
        job.status = JobStatus.applying
        job.step = "Applying patch to the live engine and rebuilding both targets..."
        await loop.run_in_executor(None, lambda: apply_integration(result))

        job.status = JobStatus.done
        job.step = None

    except IntegrationError as exc:
        job.status = JobStatus.failed
        job.step = None
        job.error = str(exc)
    except Exception as exc:  # pragma: no cover — surface anything unexpected
        job.status = JobStatus.failed
        job.step = None
        job.error = f"{type(exc).__name__}: {exc}"
    finally:
        if job.log_handler is not None:
            import logging as _logging
            _logging.getLogger().removeHandler(job.log_handler)
        job.logs_done = True

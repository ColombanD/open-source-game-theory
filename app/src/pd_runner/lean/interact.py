"""LeanInteract-backed fast proof checking (persistent REPL + env cache).

Why: every `run_lean_proof` call used to spawn a fresh `lake env lean` on a
temp file, re-loading the engine's full import closure each time (tens of
seconds, worse on OneDrive). A persistent Lean REPL loads a given import set
ONCE (cached per distinct import block), then checks candidate bodies against
that environment in seconds. Same imports ⇒ same semantics as the file
compile; a changed import block just pays one reload.

As a bonus, the REPL reports the GOAL at every `sorry`, enabling
sketch-then-fill (the AxProverBase Compiler feature).

Trust story: this backend serves the agent's ITERATION loop only. The verdict
gate (`CompileService` in proof_episodes) and the library writer still compile
the submitted file whole, from a clean process — acceptance never depends on
REPL state.

Failure policy: any infrastructure problem degrades silently to the file
backend (`try_check` returns None). Setup failures disable the checker for
the process; per-check failures keep the server (AutoLeanServer restarts
itself on crashes).
"""

from __future__ import annotations

import re
import threading
from dataclasses import dataclass, field
from pathlib import Path

from pd_runner.config import load_paths
from pd_runner.logging_config import get_logger
from pd_runner.settings import LEAN_INTERACT_ENABLED

_log = get_logger("lean.interact")

_IMPORT_RE = re.compile(r"^\s*import\s+\S+", re.MULTILINE)
_CHECK_TIMEOUT_S = 300.0


@dataclass(frozen=True)
class InteractResult:
    """Shape-compatible with LeanExecResult (returncode/stdout/stderr), plus
    the goals at `sorry` positions (the v2 sketch-then-fill seam, now live)."""

    returncode: int
    stdout: str
    stderr: str
    goals: list[str] = field(default_factory=list)


def split_imports(source: str) -> tuple[tuple[str, ...], str]:
    """Split a candidate file into (import lines, body).

    The REPL processes `import` only at environment creation, so the import
    block becomes the (cached) env and the rest is checked against it.
    Consumed header lines are BLANKED (not removed) in the body, so the line
    numbers in REPL diagnostics match the agent's full source exactly.
    """
    imports: list[str] = []
    body_lines: list[str] = []
    in_header = True
    for line in source.splitlines():
        stripped = line.strip()
        if in_header and _IMPORT_RE.match(line):
            imports.append(stripped)
            body_lines.append("")
            continue
        if in_header and imports and (not stripped or stripped.startswith("--")):
            # blank/comment lines between imports: consumed, position preserved
            body_lines.append("")
            continue
        if stripped:
            in_header = False
        body_lines.append(line)
    return tuple(imports), "\n".join(body_lines)


class InteractChecker:
    """One persistent REPL server per engine dir, env-cached by import block."""

    _MAX_CONSECUTIVE_FAILURES = 2

    def __init__(self, engine_dir: Path) -> None:
        self._engine_dir = engine_dir
        self._server = None
        self._env_cache: dict[tuple[str, ...], int] = {}
        self._lock = threading.Lock()
        self._disabled = False
        self._consecutive_failures = 0

    # -- setup ---------------------------------------------------------------

    def _ensure_server(self):
        if self._server is not None:
            return self._server
        from lean_interact import AutoLeanServer, LeanREPLConfig, LocalProject

        _log.info("Starting LeanInteract REPL for %s (first use may build the REPL)...",
                  self._engine_dir)
        # auto_build=False: the engine is kept green by the normal workflow and
        # a full `lake build` on REPL startup would be minutes of wasted wall-clock.
        config = LeanREPLConfig(
            project=LocalProject(directory=str(self._engine_dir), auto_build=False)
        )
        # macOS reports memory as near-full by design (inactive pages count), so
        # AutoLeanServer's default 0.8 total-memory guard trips chronically on
        # 16GB machines — raise it and drop the per-process cap; env commands go
        # into the session cache below so they survive server restarts.
        self._server = AutoLeanServer(
            config, max_total_memory=0.95, max_process_memory=None
        )
        _log.info("LeanInteract REPL ready")
        return self._server

    def _env_for(self, imports: tuple[str, ...]) -> int | None:
        """The cached environment for an import block (created on first use)."""
        if imports in self._env_cache:
            return self._env_cache[imports]
        from lean_interact import Command
        from lean_interact.interface import CommandResponse

        server = self._ensure_server()
        _log.info("Loading REPL environment for %d import(s)...", len(imports))
        # add_to_session_cache: the env is replayed into any restarted server,
        # so a memory-pressure restart does not orphan our cached env ids.
        response = server.run(
            Command(cmd="\n".join(imports)),
            timeout=_CHECK_TIMEOUT_S,
            add_to_session_cache=True,
        )
        if not isinstance(response, CommandResponse):
            _log.warning("REPL import load failed: %r", response)
            return None
        errors = [m for m in response.messages if m.severity == "error"]
        if errors:
            # A bad import is the AGENT's error — but we cannot cache this env;
            # report it via the file backend for exact diagnostics.
            _log.info("Import block has errors; deferring to file backend")
            return None
        self._env_cache[imports] = response.env
        return response.env

    # -- public API ----------------------------------------------------------

    def invalidate(self) -> None:
        """Drop every cached environment (call after the library mutates,
        e.g. a successful add_base_lemma)."""
        with self._lock:
            self._env_cache.clear()
        _log.info("LeanInteract env cache invalidated")

    def check(self, source: str) -> InteractResult | None:
        """Check `source` against the persistent REPL; None ⇒ use the file backend."""
        if self._disabled:
            return None
        with self._lock:
            try:
                result = self._check_locked(source)
                if result is not None:
                    self._consecutive_failures = 0
                return result
            except Exception as exc:  # noqa: BLE001 — degrade, never break the loop
                if self._server is None:
                    # Setup failed (download/build/toolchain) — do not retry per call.
                    self._disabled = True
                    _log.warning(
                        "LeanInteract unavailable (%s: %s) — falling back to "
                        "`lake env lean` for this process", type(exc).__name__, exc,
                    )
                    return None
                self._consecutive_failures += 1
                if self._consecutive_failures >= self._MAX_CONSECUTIVE_FAILURES:
                    # A struggling REPL (e.g. memory-pressure restart storms) can
                    # cost a minute per attempt — stop paying it this process.
                    self._disabled = True
                    _log.warning(
                        "LeanInteract failed %d times in a row (%s: %s) — disabling; "
                        "`lake env lean` takes over for this process",
                        self._consecutive_failures, type(exc).__name__, exc,
                    )
                else:
                    _log.warning("LeanInteract check failed (%s: %s) — falling back "
                                 "to `lake env lean` for this attempt",
                                 type(exc).__name__, exc)
                return None

    def _check_locked(self, source: str) -> InteractResult | None:
        from lean_interact import Command
        from lean_interact.interface import CommandResponse

        imports, body = split_imports(source)
        if not body.strip():
            return InteractResult(1, "", "error: empty proof body")
        env = self._env_for(imports)
        if env is None:
            return None
        server = self._ensure_server()
        response = server.run(Command(cmd=body, env=env), timeout=_CHECK_TIMEOUT_S)
        if not isinstance(response, CommandResponse):
            _log.warning("REPL check returned %r — falling back", response)
            return None

        # Header lines are blanked, not removed, so body line numbers already
        # match the full source.
        def fmt(msg) -> str:
            line = getattr(msg.start_pos, "line", 0) or 0
            return f"line {line}: [{msg.severity}] {msg.data}"

        errors = [fmt(m) for m in response.messages if m.severity == "error"]
        warnings = [fmt(m) for m in response.messages if m.severity == "warning"]
        goals = [s.goal for s in response.sorries if s.goal]
        stderr = "\n".join(errors + warnings)
        return InteractResult(
            returncode=1 if errors else 0,
            stdout="",
            stderr=stderr,
            goals=goals,
        )


_checker: InteractChecker | None = None
_checker_lock = threading.Lock()


def get_checker() -> InteractChecker | None:
    """The process-wide checker, or None when disabled by config."""
    global _checker
    if not LEAN_INTERACT_ENABLED:
        return None
    with _checker_lock:
        if _checker is None:
            _checker = InteractChecker(load_paths().lean_engine_dir)
        return _checker


def try_check(source: str) -> InteractResult | None:
    """Fast-path check; None means the caller should use the file backend."""
    checker = get_checker()
    if checker is None:
        return None
    return checker.check(source)


def invalidate_cache() -> None:
    """Invalidate cached REPL environments after a library mutation."""
    if _checker is not None:
        _checker.invalidate()

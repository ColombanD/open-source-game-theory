"""Unit tests for lean/interact.py — import splitting, env caching, error
mapping, and graceful degradation (all with a mocked REPL server)."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

from lean_interact.interface import CommandResponse

from pd_runner.lean.interact import InteractChecker, split_imports


# ---------------------------------------------------------------------------
# split_imports
# ---------------------------------------------------------------------------


def test_split_imports_basic():
    src = (
        "import PrisonersDilemma.Bots.CooperateBot\n"
        "import PrisonersDilemma.Dynamics\n"
        "\n"
        "open PD\n"
        "namespace PD.Theorems\n"
        "theorem t : True := trivial\n"
    )
    imports, body = split_imports(src)
    assert imports == (
        "import PrisonersDilemma.Bots.CooperateBot",
        "import PrisonersDilemma.Dynamics",
    )
    assert "import" not in body
    # Header lines are BLANKED, not removed: body line numbers match the source.
    body_lines = body.splitlines()
    assert body_lines[0] == "" and body_lines[1] == ""
    assert body_lines[3] == "open PD"
    assert src.splitlines()[3] == "open PD"


def test_split_imports_no_imports():
    imports, body = split_imports("theorem t : True := trivial\n")
    assert imports == ()
    assert body.startswith("theorem t")


# ---------------------------------------------------------------------------
# InteractChecker with a fake server
# ---------------------------------------------------------------------------


def _msg(severity: str, data: str, line: int = 1):
    return SimpleNamespace(
        severity=severity, data=data,
        start_pos=SimpleNamespace(line=line, column=0),
    )


def _response(env=1, messages=(), sorries=()):
    resp = CommandResponse.model_construct(
        env=env, messages=list(messages), sorries=list(sorries),
    )
    return resp


class _FakeServer:
    def __init__(self, responses):
        self.responses = list(responses)
        self.commands = []

    def run(self, command, timeout=None, add_to_session_cache=False):
        self.commands.append(command)
        return self.responses.pop(0)


def _checker_with(responses) -> tuple[InteractChecker, _FakeServer]:
    checker = InteractChecker(Path("/nonexistent"))
    server = _FakeServer(responses)
    checker._server = server
    return checker, server


_SRC = (
    "import A\nimport B\n\n"
    "theorem t : True := trivial\n"
)


def test_check_success_and_env_cache_reuse():
    checker, server = _checker_with([
        _response(env=7),                 # import-block env creation
        _response(messages=[]),           # body check 1
        _response(messages=[]),           # body check 2 (reuses env 7)
    ])
    r1 = checker.check(_SRC)
    r2 = checker.check(_SRC)
    assert r1.returncode == 0 and r2.returncode == 0
    # 3 commands total: ONE env creation + two body checks against env=7.
    assert len(server.commands) == 3
    assert server.commands[1].env == 7 and server.commands[2].env == 7


def test_check_maps_errors_with_exact_line_numbers():
    checker, _ = _checker_with([
        _response(env=1),
        _response(messages=[_msg("error", "unknown identifier 'foo'", line=4)]),
    ])
    result = checker.check(_SRC)
    assert result.returncode == 1
    # header lines are blanked, so REPL line numbers ARE full-source line numbers
    assert "line 4: [error] unknown identifier 'foo'" in result.stderr


def test_check_reports_sorry_goals():
    sorry = SimpleNamespace(goal="⊢ outcome (n+1) A B = some (.C, .C)",
                            start_pos=None, end_pos=None, proof_state=None)
    checker, _ = _checker_with([
        _response(env=1),
        _response(messages=[_msg("warning", "declaration uses 'sorry'")],
                  sorries=[sorry]),
    ])
    result = checker.check(_SRC)
    assert result.returncode == 0  # warnings only
    assert result.goals == ["⊢ outcome (n+1) A B = some (.C, .C)"]


def test_bad_import_block_defers_to_file_backend():
    checker, server = _checker_with([
        _response(env=3, messages=[_msg("error", "unknown module A")]),
    ])
    assert checker.check(_SRC) is None
    # and nothing was cached
    assert checker._env_cache == {}


def test_invalidate_clears_env_cache():
    checker, server = _checker_with([
        _response(env=7), _response(),   # first check
        _response(env=8), _response(),   # after invalidate: env re-created
    ])
    checker.check(_SRC)
    assert checker._env_cache
    checker.invalidate()
    assert checker._env_cache == {}
    checker.check(_SRC)
    assert server.commands[2].cmd.startswith("import A")  # env re-created


def test_check_exception_falls_back_without_disabling():
    class _Boom:
        def run(self, command, timeout=None, add_to_session_cache=False):
            raise TimeoutError("repl hung")

    checker = InteractChecker(Path("/nonexistent"))
    checker._server = _Boom()
    assert checker.check(_SRC) is None
    assert checker._disabled is False  # server exists → per-attempt fallback only


def test_two_consecutive_failures_disable_the_backend():
    class _Boom:
        def run(self, command, timeout=None, add_to_session_cache=False):
            raise TimeoutError("repl hung")

    checker = InteractChecker(Path("/nonexistent"))
    checker._server = _Boom()
    assert checker.check(_SRC) is None
    assert checker._disabled is False
    assert checker.check(_SRC) is None
    assert checker._disabled is True  # two strikes → file backend for the process
    # subsequent calls short-circuit without touching the server
    checker._server = None
    assert checker.check(_SRC) is None


# ---------------------------------------------------------------------------
# _run_lean_proof backend selection + goal feedback
# ---------------------------------------------------------------------------

from pd_runner.lean.interact import InteractResult
from pd_runner.llm import tools as tools_mod


def test_run_lean_proof_uses_interact_and_reports_goals(monkeypatch):
    monkeypatch.setattr(
        tools_mod, "compile_proof_source",
        lambda *a, **k: (_ for _ in ()).throw(AssertionError("file backend must not run")),
    )
    import pd_runner.lean.interact as interact_mod
    monkeypatch.setattr(
        interact_mod, "try_check",
        lambda src: InteractResult(0, "", "warning: declaration uses 'sorry'",
                                   goals=["⊢ True"]),
    )
    out = tools_mod._run_lean_proof("theorem t : True := sorry")
    assert "checked via lean-interact" in out
    assert "goals at sorry positions" in out and "⊢ True" in out


def test_run_lean_proof_falls_back_to_file_backend(monkeypatch):
    import pd_runner.lean.interact as interact_mod
    monkeypatch.setattr(interact_mod, "try_check", lambda src: None)
    monkeypatch.setattr(
        tools_mod, "compile_proof_source",
        lambda src, hint="proof_attempt": SimpleNamespace(returncode=0, stdout="ok", stderr=""),
    )
    out = tools_mod._run_lean_proof("theorem t : True := trivial")
    assert "checked via lake env lean" in out

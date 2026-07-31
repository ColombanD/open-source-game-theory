"""Unit tests for the proof pipeline: retrieval, prompts, proof_service, library_writer."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from pd_runner.llm import retrieval
from pd_runner.llm.prompts import build_system_prompt
from pd_runner.services import library_writer, proof_service, verdicts
from pd_runner.services.proof_service import ProofResult, ProofSearchError


# ---------------------------------------------------------------------------
# retrieval
# ---------------------------------------------------------------------------


def test_retrieve_few_shots_returns_bot_file_first(tmp_path: Path, monkeypatch) -> None:
    theorems_dir = tmp_path / "Theorems"
    (theorems_dir / "CooperateBot").mkdir(parents=True)
    (theorems_dir / "DefectBot").mkdir()
    (theorems_dir / "Other").mkdir()
    (theorems_dir / "CooperateBot" / "vs_DefectBot.lean").write_text(
        "theorem outcome_CooperateBot_vs_DefectBot := by rfl", encoding="utf-8"
    )
    (theorems_dir / "DefectBot" / "vs_CooperateBot.lean").write_text(
        "theorem outcome_DefectBot_vs_CooperateBot := by rfl", encoding="utf-8"
    )
    (theorems_dir / "Other" / "vs_Other.lean").write_text(
        "theorem outcome_Other_vs_Other := by rfl", encoding="utf-8"
    )

    monkeypatch.setattr(retrieval, "_THEOREMS_DIR", theorems_dir)

    shots = retrieval.retrieve_few_shots("CooperateBot", "DefectBot")
    filenames = [f for f, _ in shots]
    assert filenames[0] in {"CooperateBot/vs_DefectBot.lean", "DefectBot/vs_CooperateBot.lean"}
    assert "CooperateBot/vs_DefectBot.lean" in filenames
    assert "DefectBot/vs_CooperateBot.lean" in filenames


def test_retrieve_few_shots_respects_max_files(tmp_path: Path, monkeypatch) -> None:
    theorems_dir = tmp_path / "Theorems"
    theorems_dir.mkdir()
    for i in range(10):
        (theorems_dir / f"Bot{i}.lean").write_text(f"-- bot{i}", encoding="utf-8")

    monkeypatch.setattr(retrieval, "_THEOREMS_DIR", theorems_dir)

    shots = retrieval.retrieve_few_shots("Bot0", "Bot1", max_files=3)
    assert len(shots) <= 3


def test_retrieve_few_shots_empty_dir(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(retrieval, "_THEOREMS_DIR", tmp_path / "nonexistent")
    assert retrieval.retrieve_few_shots("CooperateBot", "DefectBot") == []


def test_list_known_outcome_theorems_returns_none_for_unknown(monkeypatch) -> None:
    monkeypatch.setattr(retrieval, "_UNIVERSAL_OUTCOME_THEOREMS", [])
    monkeypatch.setattr(retrieval, "_EXISTENTIAL_OUTCOME_THEOREMS", [])
    result = retrieval.list_known_outcome_theorems("FakeBot", "OtherBot")
    assert result == "None found."


# ---------------------------------------------------------------------------
# prompts
# ---------------------------------------------------------------------------


def _write_fake_engine(pd_dir: Path) -> None:
    pd_dir.mkdir(parents=True, exist_ok=True)
    (pd_dir / "Program.lean").write_text("-- program", encoding="utf-8")
    (pd_dir / "Dynamics.lean").write_text("-- dynamics", encoding="utf-8")
    (pd_dir / "BaseTheorems.lean").write_text("-- base-theorems", encoding="utf-8")
    (pd_dir / "ProofSystem.lean").write_text("-- proof-system", encoding="utf-8")
    base_dir = pd_dir / "Base"
    base_dir.mkdir(exist_ok=True)
    (base_dir / "Soundness.lean").write_text("-- soundness", encoding="utf-8")
    (base_dir / "AtomCerts.lean").write_text("-- atom-certs", encoding="utf-8")
    (base_dir / "Helpers.lean").write_text("-- base-helpers", encoding="utf-8")
    (base_dir / "Asymptotics.lean").write_text("-- asymptotics", encoding="utf-8")
    (base_dir / "Loeb.lean").write_text("-- loeb", encoding="utf-8")
    (base_dir / "Exclusion.lean").write_text("-- exclusion", encoding="utf-8")
    (base_dir / "Closure.lean").write_text("-- closure", encoding="utf-8")

    # Bot sources are how `_bot_uses_search` decides whether to inject the
    # search-only proof-system modules: CooperateBot has no `.search`, CupodBot does.
    bots_dir = pd_dir / "Bots"
    bots_dir.mkdir(exist_ok=True)
    (bots_dir / "CooperateBot.lean").write_text("def CooperateBot : Prog := .const .C", encoding="utf-8")
    (bots_dir / "CupodBot.lean").write_text(
        "def CupodBot (k : Nat) : Prog := .search k φ p q", encoding="utf-8"
    )


def test_build_system_prompt_includes_program_and_dynamics(tmp_path: Path, monkeypatch) -> None:
    pd_dir = tmp_path / "PrisonersDilemma"
    _write_fake_engine(pd_dir)

    import pd_runner.llm.prompts as prompts_mod
    monkeypatch.setattr(prompts_mod, "_ENGINE_PD_DIR", pd_dir)

    # Non-search matchup: core proof vocabulary (soundness + atom certificates)
    # is injected, but the heavier search-only proof-system modules are not.
    prompt = build_system_prompt("CooperateBot", "DefectBot")
    assert "-- program" in prompt
    assert "-- dynamics" in prompt
    assert "-- base-theorems" in prompt
    assert "-- soundness" in prompt
    assert "-- atom-certs" in prompt
    assert "-- proof-system" not in prompt
    assert "-- asymptotics" not in prompt
    assert "-- loeb" not in prompt
    assert "-- exclusion" not in prompt


def test_build_system_prompt_includes_proof_system_for_search_bots(
    tmp_path: Path, monkeypatch
) -> None:
    pd_dir = tmp_path / "PrisonersDilemma"
    _write_fake_engine(pd_dir)

    import pd_runner.llm.prompts as prompts_mod
    monkeypatch.setattr(prompts_mod, "_ENGINE_PD_DIR", pd_dir)

    # CupodBot uses `.search`, so the full proof-system context (axioms + the
    # explicit proof system + budget arithmetic + Löb engines + the exclusion
    # census) must be injected. Regression guard for the Base/ split: the embeds
    # must be the SPLIT modules, not just the 16-line BaseTheorems umbrella.
    prompt = build_system_prompt("CupodBot", "CooperateBot")
    assert "-- base-theorems" in prompt
    assert "-- soundness" in prompt
    assert "-- atom-certs" in prompt
    assert "-- proof-system" in prompt
    assert "-- asymptotics" in prompt
    assert "-- loeb" in prompt
    assert "-- exclusion" in prompt


# ---------------------------------------------------------------------------
# verdicts: strict-template statement checks
# ---------------------------------------------------------------------------

_GOOD_SOURCE = """\
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot

namespace PD.Theorems

theorem llm_outcome_CooperateBot_vs_DefectBot (n : Nat) :
    outcome (n+1) CooperateBot DefectBot = some (.C, .D) := by
  rfl

end PD.Theorems
"""

_THRESHOLD_SOURCE = """\
namespace PD.Theorems

theorem llm_outcome_DupocBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) (DupocBot k) = some (.C, .C) := by
  exact proof

end PD.Theorems
"""


def test_check_proved_source_accepts_template() -> None:
    assert verdicts.check_proved_source(
        _GOOD_SOURCE, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="C", submitted_right="D",
    ) == []


def test_check_proved_source_accepts_threshold_form() -> None:
    assert verdicts.check_proved_source(
        _THRESHOLD_SOURCE, left_bot="DupocBot", right_bot="DupocBot",
        submitted_left="C", submitted_right="C",
    ) == []


def test_check_proved_source_rejects_wrong_theorem_name() -> None:
    problems = verdicts.check_proved_source(
        _GOOD_SOURCE, left_bot="DefectBot", right_bot="CooperateBot",
        submitted_left="D", submitted_right="C",
    )
    assert any("llm_outcome_DefectBot_vs_CooperateBot" in p for p in problems)


def test_check_proved_source_rejects_action_mismatch() -> None:
    problems = verdicts.check_proved_source(
        _GOOD_SOURCE, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="D", submitted_right="D",
    )
    assert any("do not match" in p for p in problems)


def test_check_proved_source_rejects_oracle_premise() -> None:
    source = _GOOD_SOURCE.replace(
        "(n : Nat) :", "(n : Nat) (h : proofSearch k φ = false) :"
    )
    problems = verdicts.check_proved_source(
        source, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="C", submitted_right="D",
    )
    assert any("proofSearch" in p for p in problems)


def test_check_proved_source_rejects_forbidden_tokens() -> None:
    source = _GOOD_SOURCE.replace("rfl", "sorry")
    problems = verdicts.check_proved_source(
        source, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="C", submitted_right="D",
    )
    assert any("sorry" in p for p in problems)


def test_check_proved_source_ignores_tokens_in_comments() -> None:
    source = _GOOD_SOURCE + "\n-- do not use sorry or axiom here\n"
    assert verdicts.check_proved_source(
        source, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="C", submitted_right="D",
    ) == []


def test_check_proved_source_accepts_none_outcome() -> None:
    source = _GOOD_SOURCE.replace("= some (.C, .D)", "= none")
    assert verdicts.check_proved_source(
        source, left_bot="CooperateBot", right_bot="DefectBot",
        submitted_left="none", submitted_right="none",
    ) == []


# ---------------------------------------------------------------------------
# proof_service.search_proof (facade over the episode loop, fully mocked)
# ---------------------------------------------------------------------------


def _outcome(**overrides):
    from pd_runner.services.verdicts import ProofOutcome

    defaults = dict(
        left_bot="CooperateBot", right_bot="DefectBot", kind="proved",
        lean_source="theorem foo := by rfl", left_action="C", right_action="D",
        explanation="ok", turns_used=3,
    )
    defaults.update(overrides)
    return ProofOutcome(**defaults)


def test_search_proof_returns_result_on_proved(monkeypatch) -> None:
    from pd_runner.services import proof_episodes

    monkeypatch.setattr(proof_episodes, "run_proof_search", lambda req: _outcome())
    result = proof_service.search_proof(
        proof_service.ProofRequest("CooperateBot", "DefectBot", "C", "D")
    )
    assert result.lean_source == "theorem foo := by rfl"
    assert result.left_action == "C"
    assert result.iterations_used == 3


def test_search_proof_raises_with_kind_on_open(monkeypatch) -> None:
    from pd_runner.services import proof_episodes

    for kind, expected in (
        ("open_bistable", "open_bistable"),
        ("open_blocked", "open_blocked"),
        ("constructor_proposed", "open_constructor_proposed"),
        ("exhausted", "no_output"),
        ("error", "error"),
    ):
        monkeypatch.setattr(
            proof_episodes, "run_proof_search",
            lambda req, _k=kind: _outcome(kind=_k, lean_source=None,
                                          left_action=None, right_action=None),
        )
        with pytest.raises(ProofSearchError) as excinfo:
            proof_service.search_proof(
                proof_service.ProofRequest("CooperateBot", "DefectBot", "C", "D")
            )
        assert excinfo.value.kind == expected
        assert excinfo.value.outcome is not None
        assert excinfo.value.iterations_used == 3


def test_search_proof_outcome_captures_exceptions(monkeypatch) -> None:
    from pd_runner.services import proof_episodes

    def boom(req):
        raise RuntimeError("api exploded")

    monkeypatch.setattr(proof_episodes, "run_proof_search", boom)
    outcome = proof_service.search_proof_outcome(
        proof_service.ProofRequest("CooperateBot", "DefectBot", "C", "D")
    )
    assert outcome.kind == "error"
    assert "api exploded" in outcome.explanation


# ---------------------------------------------------------------------------
# tools._read_library_file
# ---------------------------------------------------------------------------


def test_read_library_file_returns_content(tmp_path: Path, monkeypatch) -> None:
    pd_dir = tmp_path / "PrisonersDilemma"
    (pd_dir / "Theorems").mkdir(parents=True)
    (pd_dir / "Theorems" / "CooperateBot.lean").write_text("-- cb content", encoding="utf-8")

    import pd_runner.llm.tools as tools_mod
    monkeypatch.setattr(
        tools_mod,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    from pd_runner.llm.tools import _read_library_file
    result = _read_library_file("Theorems/CooperateBot.lean")
    assert result == "-- cb content"


def test_read_library_file_rejects_path_traversal(tmp_path: Path, monkeypatch) -> None:
    import pd_runner.llm.tools as tools_mod
    monkeypatch.setattr(
        tools_mod,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    from pd_runner.llm.tools import _read_library_file
    result = _read_library_file("../../etc/passwd")
    assert "Error" in result


def test_read_library_file_missing_file(tmp_path: Path, monkeypatch) -> None:
    (tmp_path / "PrisonersDilemma").mkdir()
    import pd_runner.llm.tools as tools_mod
    monkeypatch.setattr(
        tools_mod,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    from pd_runner.llm.tools import _read_library_file
    result = _read_library_file("Theorems/Nonexistent.lean")
    assert "not found" in result


# ---------------------------------------------------------------------------
# library_writer
# ---------------------------------------------------------------------------


def _setup_theorems_layout(tmp_path: Path) -> tuple[Path, Path]:
    """Create the per-pair layout the writer targets (2026-07-27 refactor).

    Returns (theorems_dir, index_file). Proofs are written to
    `Theorems/<LeftBot>/vs_<RightBot>.lean` and their import lines appended
    to the engine's ROOT `PrisonersDilemma.lean`, which must already exist.
    """
    theorems_dir = tmp_path / "PrisonersDilemma" / "Theorems"
    theorems_dir.mkdir(parents=True)
    index = tmp_path / "PrisonersDilemma.lean"
    index.write_text("-- root index\n", encoding="utf-8")
    return theorems_dir, index


def _cooperate_vs_defect_result() -> ProofResult:
    return ProofResult(
        left_bot="CooperateBot",
        right_bot="DefectBot",
        left_action="C",
        right_action="D",
        lean_source="theorem foo := by rfl",
        iterations_used=1,
    )


def test_write_proof_dry_run_does_not_write(tmp_path: Path, monkeypatch) -> None:
    theorems_dir, _ = _setup_theorems_layout(tmp_path)

    monkeypatch.setattr(
        library_writer,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    write_result = library_writer.write_proof_to_library(
        _cooperate_vs_defect_result(), human_accept=False, dry_run=True
    )

    expected = theorems_dir / "CooperateBot" / "vs_DefectBot.lean"
    assert write_result.path == expected
    assert write_result.build_ok is True
    assert not expected.exists()


def test_write_proof_refuses_to_overwrite(tmp_path: Path, monkeypatch) -> None:
    theorems_dir, _ = _setup_theorems_layout(tmp_path)
    existing = theorems_dir / "CooperateBot" / "vs_DefectBot.lean"
    existing.parent.mkdir()
    existing.write_text("-- already exists", encoding="utf-8")

    monkeypatch.setattr(
        library_writer,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    with pytest.raises(library_writer.LibraryWriteError, match="already exists"):
        library_writer.write_proof_to_library(
            _cooperate_vs_defect_result(), human_accept=False, dry_run=False
        )


def test_write_proof_rolls_back_on_build_failure(tmp_path: Path, monkeypatch) -> None:
    from pd_runner.lean.executor import LeanExecResult

    theorems_dir, index = _setup_theorems_layout(tmp_path)

    monkeypatch.setattr(
        library_writer,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )
    monkeypatch.setattr(
        library_writer,
        "build_lean_project",
        lambda _: LeanExecResult("lake build", 1, "", "build error"),
    )

    with pytest.raises(library_writer.LibraryWriteError, match="lake build failed"):
        library_writer.write_proof_to_library(
            _cooperate_vs_defect_result(), human_accept=False, dry_run=False
        )

    # Both the proof file and the appended index import line are rolled back.
    assert not (theorems_dir / "CooperateBot" / "vs_DefectBot.lean").exists()
    assert "vs_DefectBot" not in index.read_text(encoding="utf-8")


def test_write_proof_writes_and_builds_successfully(tmp_path: Path, monkeypatch) -> None:
    from pd_runner.lean.executor import LeanExecResult

    theorems_dir, index = _setup_theorems_layout(tmp_path)

    monkeypatch.setattr(
        library_writer,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )
    monkeypatch.setattr(
        library_writer,
        "build_lean_project",
        lambda _: LeanExecResult("lake build", 0, "Build OK", ""),
    )

    write_result = library_writer.write_proof_to_library(
        _cooperate_vs_defect_result(), human_accept=False
    )

    expected = theorems_dir / "CooperateBot" / "vs_DefectBot.lean"
    assert expected.exists()
    assert "theorem foo" in expected.read_text()
    assert write_result.build_ok is True
    # The import line was appended to the root index.
    assert (
        "import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot"
        in index.read_text(encoding="utf-8")
    )


# ---------------------------------------------------------------------------
# library_search.search_declarations
# ---------------------------------------------------------------------------


def _write_search_fixture(root: Path) -> Path:
    pd = root / "PrisonersDilemma"
    (pd / "Base").mkdir(parents=True)
    (pd / "Theorems" / "OBot").mkdir(parents=True)
    (pd / "Research" / "Spikes").mkdir(parents=True)
    (pd / "Base" / "Exclusion.lean").write_text(
        "theorem no_provable_probeFirst_tail (k : Nat)\n"
        "    (h : tailTo p q) :\n"
        "    ¬ Pf k φ := by\n"
        "  exact proof\n\n"
        "def helperDef : Nat := 3\n",
        encoding="utf-8",
    )
    (pd / "Theorems" / "OBot" / "Helpers.lean").write_text(
        "theorem obot_floor_census : ¬ Pf k (plays OBot q .D) := by exact x\n",
        encoding="utf-8",
    )
    (pd / "Research" / "Spikes" / "Old.lean").write_text(
        "theorem no_provable_spike_only : True := trivial\n", encoding="utf-8"
    )
    return pd


def test_search_declarations_by_name_and_signature(tmp_path: Path) -> None:
    from pd_runner.llm.library_search import search_declarations

    pd = _write_search_fixture(tmp_path)
    by_name = search_declarations("probeFirst", engine_pd_dir=pd)
    assert [m.name for m in by_name] == ["no_provable_probeFirst_tail"]
    assert by_name[0].name_hit and by_name[0].line == 1
    assert "¬ Pf k φ" in by_name[0].signature
    assert ":=" not in by_name[0].signature.split("¬ Pf k φ")[-1]

    # signature-content hit (tailTo appears only in the statement)
    by_sig = search_declarations("tailTo", engine_pd_dir=pd)
    assert [m.name for m in by_sig] == ["no_provable_probeFirst_tail"]
    assert not by_sig[0].name_hit


def test_search_declarations_excludes_research_and_hidden_bots(tmp_path: Path) -> None:
    from pd_runner.llm.library_search import search_declarations

    pd = _write_search_fixture(tmp_path)
    all_no_provable = search_declarations("no_provable|obot_floor", engine_pd_dir=pd)
    assert {m.name for m in all_no_provable} == {
        "no_provable_probeFirst_tail", "obot_floor_census",
    }  # spike excluded
    hidden = search_declarations(
        "no_provable|obot_floor", engine_pd_dir=pd, hidden_bots=frozenset({"OBot"})
    )
    assert {m.name for m in hidden} == {"no_provable_probeFirst_tail"}


def test_search_declarations_bad_regex_falls_back_to_literal(tmp_path: Path) -> None:
    from pd_runner.llm.library_search import search_declarations

    pd = _write_search_fixture(tmp_path)
    assert search_declarations("probeFirst(", engine_pd_dir=pd) == []
    assert search_declarations("probeFirst_", engine_pd_dir=pd) != []


# ---------------------------------------------------------------------------
# proof_episodes.run_proof_search: open-verdict one-shot retry
# ---------------------------------------------------------------------------


def _episode_result(verdict: dict | None, end_reason: str = "verdict"):
    from pd_runner.llm.client import EpisodeResult, UsageTotals

    return EpisodeResult(
        verdict_input=verdict,
        end_reason=end_reason if verdict is None else "verdict",
        turns_used=1,
        tool_calls_used=0,
        usage=UsageTotals(),
        final_text="",
        messages=[],
    )


def _stub_episode_loop(monkeypatch, results: list):
    """Stub every heavy dependency of run_proof_search; script the episodes."""
    from pd_runner.services import proof_episodes as pe

    user_contents: list[str] = []
    persisted: list[dict] = []

    class FakeClient:
        def __init__(self, **kwargs):
            pass

        def run_episode(self, user_content, handler, **kwargs):
            user_contents.append(user_content)
            return results[len(user_contents) - 1]

    monkeypatch.setattr(pe, "AnthropicClient", FakeClient)
    monkeypatch.setattr(pe, "retrieve_few_shots", lambda *a, **k: [])
    monkeypatch.setattr(pe, "list_known_outcome_theorems", lambda *a, **k: "")
    monkeypatch.setattr(pe, "build_system_prompt_blocks", lambda *a, **k: ["sys"])
    monkeypatch.setattr(pe, "proof_request_message", lambda **k: "user")
    monkeypatch.setattr(pe, "_make_tool_handler", lambda *a, **k: None)
    monkeypatch.setattr(pe, "_persist_episode", lambda *a, **k: persisted.append(dict(k)))
    return user_contents, persisted


def test_first_open_verdict_triggers_exactly_one_retry(monkeypatch) -> None:
    from pd_runner.services.proof_episodes import run_proof_search

    open1 = {"verdict": "open_blocked", "explanation": "guard loop with no Löb rescue"}
    open2 = {"verdict": "open_bistable", "explanation": "still open on re-derivation"}
    user_contents, persisted = _stub_episode_loop(
        monkeypatch, [_episode_result(open1), _episode_result(open2)]
    )

    outcome = run_proof_search(verdicts.ProofRequest("BotA", "BotB", max_episodes=3))

    # The second open verdict is final — no third episode despite max_episodes=3.
    assert outcome.kind == "open_bistable"
    assert outcome.episodes_used == 2
    assert len(user_contents) == 2
    # The retry episode sees the prior open verdict and its explanation.
    assert "open_blocked" in user_contents[1]
    assert "guard loop with no Löb rescue" in user_contents[1]
    # The retried episode is not persisted as final; the accepting one is.
    assert [p["final"] for p in persisted] == [False, True]


def test_proved_verdict_ends_run_without_retry(monkeypatch) -> None:
    from pd_runner.services.proof_episodes import run_proof_search

    proved = {
        "verdict": "proved", "lean_source": "theorem t : True := trivial",
        "left_action": "C", "right_action": "D", "explanation": "done",
    }
    user_contents, _ = _stub_episode_loop(monkeypatch, [_episode_result(proved)])

    outcome = run_proof_search(verdicts.ProofRequest("BotA", "BotB", max_episodes=3))

    assert outcome.kind == "proved"
    assert len(user_contents) == 1


def test_open_verdict_on_last_episode_is_final(monkeypatch) -> None:
    from pd_runner.services.proof_episodes import run_proof_search

    open1 = {"verdict": "open_blocked", "explanation": "blocked"}
    user_contents, persisted = _stub_episode_loop(monkeypatch, [_episode_result(open1)])

    outcome = run_proof_search(verdicts.ProofRequest("BotA", "BotB", max_episodes=1))

    assert outcome.kind == "open_blocked"
    assert len(user_contents) == 1
    assert persisted[0]["final"] is True


def test_retry_without_verdict_falls_back_to_open_verdict(monkeypatch) -> None:
    from pd_runner.services.proof_episodes import run_proof_search

    open1 = {"verdict": "open_blocked", "explanation": "blocked"}
    user_contents, _ = _stub_episode_loop(
        monkeypatch, [_episode_result(open1), _episode_result(None, end_reason="turn_cap")]
    )

    outcome = run_proof_search(verdicts.ProofRequest("BotA", "BotB", max_episodes=2))

    # The retry episode hit the turn cap with no verdict — the run falls back
    # to the open verdict that triggered the retry instead of "exhausted".
    assert outcome.kind == "open_blocked"
    assert outcome.explanation == "blocked"
    assert len(user_contents) == 2

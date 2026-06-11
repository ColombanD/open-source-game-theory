"""Unit tests for the proof pipeline: retrieval, prompts, proof_service, library_writer."""

from __future__ import annotations

from pathlib import Path
from types import SimpleNamespace

import pytest

from pd_runner.llm import retrieval
from pd_runner.llm.prompts import build_system_prompt
from pd_runner.services import library_writer, proof_service
from pd_runner.services.proof_service import ProofResult, ProofSearchError, _extract_lean_source


# ---------------------------------------------------------------------------
# retrieval
# ---------------------------------------------------------------------------


def test_retrieve_few_shots_returns_bot_file_first(tmp_path: Path, monkeypatch) -> None:
    theorems_dir = tmp_path / "Theorems"
    theorems_dir.mkdir()
    (theorems_dir / "CooperateBot.lean").write_text("-- cb", encoding="utf-8")
    (theorems_dir / "DefectBot.lean").write_text("-- db", encoding="utf-8")
    (theorems_dir / "Other.lean").write_text("-- other", encoding="utf-8")

    monkeypatch.setattr(retrieval, "_THEOREMS_DIR", theorems_dir)

    shots = retrieval.retrieve_few_shots("CooperateBot", "DefectBot")
    filenames = [f for f, _ in shots]
    assert filenames[0] in {"CooperateBot.lean", "DefectBot.lean"}
    assert "CooperateBot.lean" in filenames
    assert "DefectBot.lean" in filenames


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
    (pd_dir / "Axioms.lean").write_text("-- axioms", encoding="utf-8")
    (pd_dir / "Derivation.lean").write_text("-- derivation", encoding="utf-8")
    (pd_dir / "SizeLemmas.lean").write_text("-- size-lemmas", encoding="utf-8")

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

    # Non-search matchup: core proof vocabulary is injected, but the heavier
    # search-only proof-system modules are not.
    prompt = build_system_prompt("CooperateBot", "DefectBot")
    assert "-- program" in prompt
    assert "-- dynamics" in prompt
    assert "-- base-theorems" in prompt
    assert "-- axioms" not in prompt
    assert "-- derivation" not in prompt
    assert "-- size-lemmas" not in prompt


def test_build_system_prompt_includes_proof_system_for_search_bots(
    tmp_path: Path, monkeypatch
) -> None:
    pd_dir = tmp_path / "PrisonersDilemma"
    _write_fake_engine(pd_dir)

    import pd_runner.llm.prompts as prompts_mod
    monkeypatch.setattr(prompts_mod, "_ENGINE_PD_DIR", pd_dir)

    # CupodBot uses `.search`, so the full proof-system context (axioms +
    # explicit derivation system + budget lemmas) must be injected. This is the
    # regression guard for the engine reform that moved `atom_complete` out of
    # `Axioms.lean` into `BaseTheorems.lean` and added `Derivation`/`SizeLemmas`.
    prompt = build_system_prompt("CupodBot", "CooperateBot")
    assert "-- base-theorems" in prompt
    assert "-- axioms" in prompt
    assert "-- derivation" in prompt
    assert "-- size-lemmas" in prompt


# ---------------------------------------------------------------------------
# proof_service._extract_lean_source
# ---------------------------------------------------------------------------


def test_extract_lean_source_returns_last_block() -> None:
    text = "first\n```lean\nfoo\n```\nsome text\n```lean\nbar\n```\ndone"
    assert _extract_lean_source(text) == "bar"


def test_extract_lean_source_returns_none_when_absent() -> None:
    assert _extract_lean_source("no code fence here") is None


def test_extract_lean_source_strips_whitespace() -> None:
    text = "```lean\n\n  theorem foo := by rfl\n\n```"
    assert _extract_lean_source(text) == "theorem foo := by rfl"


# ---------------------------------------------------------------------------
# proof_service.search_proof (fully mocked)
# ---------------------------------------------------------------------------


def test_search_proof_returns_result_on_success(tmp_path: Path, monkeypatch) -> None:
    lean_source = "theorem foo := by rfl"

    monkeypatch.setattr(proof_service, "retrieve_few_shots", lambda *a, **kw: [])
    monkeypatch.setattr(proof_service, "list_known_outcome_theorems", lambda *a, **kw: "None found.")
    monkeypatch.setattr(proof_service, "build_system_prompt", lambda *a: "system")
    # `search_proof` persists every attempt to `generated/outcomes/`; redirect that
    # to a tmp dir so the test does not clobber the committed fixtures.
    monkeypatch.setattr(proof_service, "_outcomes_dir", lambda: tmp_path)
    monkeypatch.setattr(
        proof_service.AnthropicClient,
        "run",
        lambda self, msg, tool_handler=None: f"PROOF COMPLETE\n```lean\n{lean_source}\n```",
    )

    result = proof_service.search_proof(
        proof_service.ProofRequest("CooperateBot", "DefectBot", "C", "D")
    )
    assert result.lean_source == lean_source
    assert result.left_bot == "CooperateBot"
    assert result.right_bot == "DefectBot"


def test_search_proof_raises_when_no_lean_block(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(proof_service, "retrieve_few_shots", lambda *a, **kw: [])
    monkeypatch.setattr(proof_service, "list_known_outcome_theorems", lambda *a, **kw: "None found.")
    monkeypatch.setattr(proof_service, "build_system_prompt", lambda *a: "system")
    monkeypatch.setattr(proof_service, "_outcomes_dir", lambda: tmp_path)
    monkeypatch.setattr(
        proof_service.AnthropicClient,
        "run",
        lambda self, msg, tool_handler=None: "I give up.",
    )

    with pytest.raises(ProofSearchError, match="did not produce"):
        proof_service.search_proof(
            proof_service.ProofRequest("CooperateBot", "DefectBot", "C", "D")
        )


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


def _setup_llm_generations(tmp_path: Path) -> tuple[Path, Path]:
    """Create the LlmGenerations layout the writer targets.

    Returns (llm_dir, index_file). Proofs are written to
    `Theorems/LlmGenerations/` and their import lines appended to the
    `Theorems/LlmGenerations.lean` index, which must already exist.
    """
    theorems_dir = tmp_path / "PrisonersDilemma" / "Theorems"
    llm_dir = theorems_dir / "LlmGenerations"
    llm_dir.mkdir(parents=True)
    index = theorems_dir / "LlmGenerations.lean"
    index.write_text("-- LlmGenerations index\n", encoding="utf-8")
    return llm_dir, index


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
    llm_dir, _ = _setup_llm_generations(tmp_path)

    monkeypatch.setattr(
        library_writer,
        "load_paths",
        lambda: SimpleNamespace(lean_engine_dir=tmp_path),
    )

    write_result = library_writer.write_proof_to_library(
        _cooperate_vs_defect_result(), human_accept=False, dry_run=True
    )

    expected = llm_dir / "outcome_CooperateBot_vs_DefectBot.lean"
    assert write_result.path == expected
    assert write_result.build_ok is True
    assert not expected.exists()


def test_write_proof_refuses_to_overwrite(tmp_path: Path, monkeypatch) -> None:
    llm_dir, _ = _setup_llm_generations(tmp_path)
    existing = llm_dir / "outcome_CooperateBot_vs_DefectBot.lean"
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

    llm_dir, index = _setup_llm_generations(tmp_path)

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
    assert not (llm_dir / "outcome_CooperateBot_vs_DefectBot.lean").exists()
    assert "outcome_CooperateBot_vs_DefectBot" not in index.read_text(encoding="utf-8")


def test_write_proof_writes_and_builds_successfully(tmp_path: Path, monkeypatch) -> None:
    from pd_runner.lean.executor import LeanExecResult

    llm_dir, index = _setup_llm_generations(tmp_path)

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

    expected = llm_dir / "outcome_CooperateBot_vs_DefectBot.lean"
    assert expected.exists()
    assert "theorem foo" in expected.read_text()
    assert write_result.build_ok is True
    # The import line was appended to the index.
    assert "outcome_CooperateBot_vs_DefectBot" in index.read_text(encoding="utf-8")

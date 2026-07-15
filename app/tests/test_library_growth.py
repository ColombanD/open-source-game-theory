"""Tests for the OUTCOME-OPEN escalation-ladder tools (lemma library + constructor proposals)."""

from __future__ import annotations

from dataclasses import dataclass

import pytest

from pd_runner.services import constructor_proposals, lemma_library
from pd_runner.services.lemma_library import _check_source, LemmaRejected, add_lemma


@dataclass
class _FakeResult:
    returncode: int
    stdout: str = ""
    stderr: str = ""


# ---------------------------------------------------------------------------
# Static guards: everything that would extend the trusted base is rejected.
# ---------------------------------------------------------------------------

@pytest.mark.parametrize(
    "source",
    [
        "axiom evil : ∀ k φ, Pf k φ",
        "theorem h : True := by sorry",
        "theorem h : True := by admit",
        "inductive Evil : Prop where | mk : Evil",
        "theorem h : 2 + 2 = 4 := by native_decide",
        "unsafe def f : Nat := 0",
        "@[extern \"c\"] def f : Nat := 0",
        "theorem t : True := trivial\nimplemented_by f",
        "macro \"boom\" : tactic => `(tactic| sorry)",
        "def MyBot : Prog := .const .C",           # bot redefinition
        "import PrisonersDilemma\ntheorem t : True := trivial",  # no imports
        "namespace Foo\ntheorem t : True := trivial",            # no namespaces
        "-- just a comment, no declaration",
    ],
)
def test_lemma_guards_reject(source: str) -> None:
    with pytest.raises(LemmaRejected):
        _check_source(source)


def test_lemma_guards_accept_plain_theorem() -> None:
    _check_source("theorem t (k : Nat) : k ≤ k := Nat.le_refl k")


# ---------------------------------------------------------------------------
# Transactionality: a failed build restores the file byte-for-byte.
# ---------------------------------------------------------------------------

def test_add_lemma_rolls_back_on_build_failure(tmp_path, monkeypatch) -> None:
    target = tmp_path / "PrisonersDilemma" / "Theorems" / "LlmGenerations" / "LlmLemmas.lean"
    index = tmp_path / "PrisonersDilemma" / "Theorems" / "LlmGenerations.lean"
    index.parent.mkdir(parents=True)
    index.write_text("", encoding="utf-8")

    @dataclass
    class _FakePaths:
        lean_engine_dir = tmp_path

    monkeypatch.setattr(lemma_library, "load_paths", lambda: _FakePaths())

    ok = add_lemma("good", "theorem g : True := trivial", build=lambda *a, **k: _FakeResult(0))
    assert ok.startswith("OK")
    before = target.read_text(encoding="utf-8")
    assert "theorem g : True := trivial" in before

    failed = add_lemma(
        "bad", "theorem b : False := trivial",
        build=lambda *a, **k: _FakeResult(1, stderr="type mismatch"),
    )
    assert failed.startswith("BUILD FAILED")
    assert target.read_text(encoding="utf-8") == before      # byte-identical rollback


def test_add_lemma_bootstrap_indexes_module(tmp_path, monkeypatch) -> None:
    index = tmp_path / "PrisonersDilemma" / "Theorems" / "LlmGenerations.lean"
    index.parent.mkdir(parents=True)
    index.write_text("import PrisonersDilemma.Theorems.LlmGenerations.Something\n", encoding="utf-8")

    @dataclass
    class _FakePaths:
        lean_engine_dir = tmp_path

    monkeypatch.setattr(lemma_library, "load_paths", lambda: _FakePaths())
    add_lemma("g", "theorem g : True := trivial", build=lambda *a, **k: _FakeResult(0))
    assert "import PrisonersDilemma.Theorems.LlmGenerations.LlmLemmas" in index.read_text(encoding="utf-8")


# ---------------------------------------------------------------------------
# Constructor proposals: certificate gate + bundle contents.
# ---------------------------------------------------------------------------

_RATIONALE = "x" * 100  # long enough to pass the thin-rationale guard


def test_proposal_rejects_holey_certificate() -> None:
    out = constructor_proposals.propose(
        "r", "| r : Pf k φ", "theorem t : True := by sorry", _RATIONALE, "u")
    assert out.startswith("REJECTED")


def test_proposal_rejects_thin_rationale() -> None:
    out = constructor_proposals.propose(
        "r", "| r : Pf k φ", "theorem t : True := trivial", "seems fine", "u")
    assert out.startswith("REJECTED")


def test_proposal_records_bundle_on_compiling_certificate(tmp_path, monkeypatch) -> None:
    @dataclass
    class _FakePaths:
        lean_engine_dir = tmp_path
        generated_lean_dir = tmp_path / "generated" / "lean"

    monkeypatch.setattr(constructor_proposals, "load_paths", lambda: _FakePaths())
    monkeypatch.setattr(constructor_proposals, "run_lean_proof_file", lambda *a: _FakeResult(0))

    out = constructor_proposals.propose(
        "eqSym", "| eqSym : ...", "theorem eqSym_sound : True := trivial", _RATIONALE,
        "symmetric guards")
    assert out.startswith("PROPOSAL RECORDED")
    bundle = tmp_path / "generated" / "constructor_proposals" / "eqSym"
    assert (bundle / "proposal.md").exists()
    assert (bundle / "soundness_certificate.lean").exists()
    assert "awaiting human review" in (bundle / "proposal.md").read_text(encoding="utf-8")


def test_proposal_not_recorded_on_failing_certificate(tmp_path, monkeypatch) -> None:
    @dataclass
    class _FakePaths:
        lean_engine_dir = tmp_path
        generated_lean_dir = tmp_path / "generated" / "lean"

    monkeypatch.setattr(constructor_proposals, "load_paths", lambda: _FakePaths())
    monkeypatch.setattr(constructor_proposals, "run_lean_proof_file",
                        lambda *a: _FakeResult(1, stderr="unknown identifier"))

    out = constructor_proposals.propose(
        "bad", "| bad : ...", "theorem nope : False := trivial", _RATIONALE, "n/a")
    assert out.startswith("CERTIFICATE FAILED")
    assert not (tmp_path / "generated" / "constructor_proposals" / "bad").exists()


# ---------------------------------------------------------------------------
# Registration policy: growth tools are production-only.
# ---------------------------------------------------------------------------

def test_growth_tools_not_registered_with_exclude_bots() -> None:
    from pd_runner.llm.client import ToolHandler
    from pd_runner.llm.tools import register_lean_tools

    prod = ToolHandler()
    register_lean_tools(prod, exclude_bots=frozenset())
    harness = ToolHandler()
    register_lean_tools(harness, exclude_bots=frozenset({"DupocBot"}))

    assert "add_base_lemma" in prod._registry and "propose_pf_constructor" in prod._registry
    assert "add_base_lemma" not in harness._registry
    assert "propose_pf_constructor" not in harness._registry

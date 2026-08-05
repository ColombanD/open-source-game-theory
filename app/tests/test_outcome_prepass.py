"""Registry-arity and spec-derivation guards for the outcome prepass.

The bug these exist to prevent: a bot taking two `Nat` budgets applied to one
argument elaborates to `Nat → Prog`, not `Prog`. `outcomeG` then yields nothing
and EVERY cell reads `undetermined`/`oom` — indistinguishable in the output from
a genuine Löb boundary. `OptimBot` was mis-registered this way until 2026-08-05
and its entire row of results was silently meaningless.

`test_registry_arity_matches_source` is the regression test proper: it
cross-checks every REGISTRY template against the binder list in the bot's own
Lean source, so a future two-budget bot cannot be added single-arity.
"""

from __future__ import annotations

import pytest

from pd_runner.config import load_paths
from pd_runner.eval.outcome_prepass import (
    REGISTRY,
    BotSpec,
    arity_from_source,
    bot_spec_from_source,
    guard_from_source,
    verify_registry_arity,
)


def test_registry_arity_matches_source() -> None:
    """Every REGISTRY entry applies exactly as many budgets as its `def` takes."""
    problems = verify_registry_arity(load_paths().lean_engine_dir)
    assert problems == {}, "registry/source arity mismatch:\n" + "\n".join(
        f"  {name}: {complaint}" for name, complaint in problems.items()
    )


def test_optimbot_is_two_budget() -> None:
    """The specific bug: OptimBot takes (kOpp kSelf), so its template needs two."""
    assert REGISTRY["OptimBot"].arity == 2
    assert REGISTRY["LegibleBot"].arity == 2


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ("def B : Prog := .const Action.C", 0),
        ("def B (k : Nat) : Prog :=\n  .search k", 1),
        ("def B (kOpp kSelf : Nat) : Prog :=\n  .search kOpp", 2),
        ("def B (a : Nat) (b : Nat) : Prog :=\n  .search a", 2),
        ("def B (a b c : Nat) : Prog := x", 3),
    ],
)
def test_arity_from_source(source: str, expected: int) -> None:
    assert arity_from_source("B", source) == expected


def test_arity_from_source_rejects_missing_def() -> None:
    with pytest.raises(ValueError, match="no `def B"):
        arity_from_source("B", "def Other (k : Nat) : Prog := x")


def test_arity_only_matches_the_named_bot() -> None:
    """A file defining several bots must not leak another bot's binders."""
    source = "def Helper (a b : Nat) : Prog := x\ndef B (k : Nat) : Prog := y\n"
    assert arity_from_source("B", source) == 1
    assert arity_from_source("Helper", source) == 2


@pytest.mark.parametrize(
    ("source", "expected"),
    [
        ("def B : Prog := .const Action.C", None),
        ("def B (k : Nat) : Prog := .search k (.plays .opp .self Action.C) a b", "plays"),
        ("def B (k : Nat) : Prog := .search k (.neg (.plays .opp .self Action.C)) a b", "neg"),
        ("def B (k : Nat) : Prog := .search k (.impl x y) a b", "impl"),
        ("def B (k : Nat) : Prog := .search k (.eq .opp (.bot X)) a b", "eq"),
        ("def B (k j : Nat) : Prog := .search k (.box j x) a b", "box"),
    ],
)
def test_guard_from_source(source: str, expected: str | None) -> None:
    assert guard_from_source(source) == expected


def test_bot_spec_from_source_round_trips_registry() -> None:
    """Specs derived from source reproduce the hand-written registry entries."""
    engine_dir = load_paths().lean_engine_dir
    for name, spec in REGISTRY.items():
        path = engine_dir.joinpath(*spec.module.split(".")).with_suffix(".lean")
        derived = bot_spec_from_source(name, spec.module, path.read_text(encoding="utf-8"))
        assert derived == spec, f"{name}: derived {derived} != registry {spec}"


def test_botspec_arity_counts_template_slots() -> None:
    assert BotSpec("M", "B", None).arity == 0
    assert BotSpec("M", "B {k}", "plays").arity == 1
    assert BotSpec("M", "B {k} {k}", "plays").arity == 2

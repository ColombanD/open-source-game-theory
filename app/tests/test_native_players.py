"""Native tau players — ConfidenceBot, the MAX aggregator over Dupoc's test (2026-08-27).

A tau player is a (per-hypothesis TEST, AGGREGATOR) pair. Lifts aggregate by
`sum ≥ α`; ConfidenceBot by `max ≥ α`. Two facts are load-bearing and tested here:

* in the HYPOTHESIS role ConfidenceBot IS DupocBot (the aggregator is invisible at
  point mass), so its matrix cells are a clone of Dupoc's — and the kernel certifies
  that clone through the tau roster (`test_def4_compare` covers the rows; here we
  check the Python matrix reproduces it);
* as a PLAYER it is the lift of no base bot: the max is not a threshold of any
  linear mass (`confidence_not_linear` in Lean; the same three-signal witness here).
"""

from __future__ import annotations

import pytest

from pd_runner.tau.matrix import NATIVE_PLAYERS, ZOOS, load_tau_matrix
from pd_runner.tau.play import (
    alpha_breakpoints,
    coop_mass,
    decision_mass,
    max_mass,
    tau_match,
    tau_play,
)
from pd_runner.tau.signal import Signal, signal_family
from pd_runner.tau.sweep import anchor_holds, base_tournament_cells, run_tournament


@pytest.fixture(scope="module")
def matrix():
    return ZOOS["default+confidence"].load()


def test_zoo_registers_the_native(matrix) -> None:
    zoo = ZOOS["default+confidence"]
    assert zoo.natives == ("ConfidenceBot",)
    assert "ConfidenceBot" in matrix.bots and "DupocBot" in matrix.bots
    assert matrix.aggregator("ConfidenceBot") == "max"
    assert matrix.aggregator("DupocBot") == "sum"
    assert matrix.source_bot("ConfidenceBot") == "DupocBot"
    assert matrix.source_bot("DupocBot") == "DupocBot"
    assert NATIVE_PLAYERS["ConfidenceBot"].base == "DupocBot"


def test_native_cells_are_clones_of_the_base(matrix) -> None:
    """In the hypothesis role ConfidenceBot is Dupoc's instance: every cell
    involving it copies the corresponding Dupoc cell, both orientations, and is
    marked as a clone. The cloned proof is the base theorem's."""
    for other in matrix.bots:
        base_other = matrix.source_bot(other)
        row = matrix.cell("ConfidenceBot", other)
        assert (row.row_action, row.col_action) == (
            matrix.action("DupocBot", base_other), matrix.action(base_other, "DupocBot"))
        assert row.clone_of == ("DupocBot", base_other)
        col = matrix.cell(other, "ConfidenceBot")
        assert (col.row_action, col.col_action) == (
            matrix.action(base_other, "DupocBot"), matrix.action("DupocBot", base_other))
        assert col.clone_of == (base_other, "DupocBot")
    # the base's own cells are untouched
    assert matrix.cell("DupocBot", "CooperateBot").clone_of is None
    assert matrix.is_fully_proven


def test_native_base_need_not_be_in_the_zoo() -> None:
    """The clone is looked up by base name, so a zoo may hold the native alone."""
    m = load_tau_matrix(bots=("CooperateBot", "DefectBot", "ConfidenceBot"), hypothetical_cells={})
    assert m.action("ConfidenceBot", "CooperateBot") == "C"
    assert m.action("ConfidenceBot", "DefectBot") == "D"
    assert m.action("ConfidenceBot", "ConfidenceBot") == "C"   # Dupoc's Löbian self-play


def test_anchor_pointwise_for_the_native(matrix) -> None:
    """At point mass the aggregator is invisible: ConfidenceBot plays what Dupoc
    plays, for every α ∈ (0, 1] — the t = 1 anchor."""
    for hyp in matrix.bots:
        signal = Signal.point_mass(hyp)
        assert max_mass(matrix, "ConfidenceBot", signal) in (0.0, 1.0)
        for alpha in (1e-9, 0.25, 0.5, 0.75, 1.0):
            assert tau_play(matrix, "ConfidenceBot", alpha, signal) == matrix.action("DupocBot", hyp)


def test_anchor_tournament_with_the_native(matrix) -> None:
    for alpha in (0.25, 0.5, 0.75, 1.0):
        assert anchor_holds(matrix, alpha)
    assert run_tournament(matrix, 1.0, 0.5).cells == base_tournament_cells(matrix)


def test_max_is_not_the_sum(matrix) -> None:
    """Split the signal between two hypotheses Dupoc cooperates with: the lift's
    C-mass is 1 (cooperates at any α ≤ 1), the native's max-mass is ½ (defects
    above α = ½). Same bits, different aggregator."""
    signal = Signal(weights={"CooperateBot": 0.5, "TitForTatBot": 0.5})
    assert matrix.cooperates("DupocBot", "CooperateBot")
    assert matrix.cooperates("DupocBot", "TitForTatBot")
    assert coop_mass(matrix, "DupocBot", signal) == pytest.approx(1.0)
    assert max_mass(matrix, "ConfidenceBot", signal) == pytest.approx(0.5)
    assert decision_mass(matrix, "ConfidenceBot", signal) == pytest.approx(0.5)
    assert tau_play(matrix, "DupocBot", 0.6, signal) == "C"
    assert tau_play(matrix, "ConfidenceBot", 0.6, signal) == "D"
    assert tau_play(matrix, "ConfidenceBot", 0.5, signal) == "C"   # `≥ α`
    assert 0.5 in [round(b, 9) for b in alpha_breakpoints(matrix, {"x": signal})]


def test_native_is_not_a_threshold_of_any_mass(matrix) -> None:
    """The Python restatement of Lean's `confidence_not_linear`: on the signals
    δ_coop, ½δ_coop + ½δ_tft, δ_tft the native plays C, D, C at α = 1, and no
    threshold-of-a-linear-mass player can — the middle mass is the average of the
    outer two, so it cannot be the only one below the threshold."""
    w1 = Signal.point_mass("CooperateBot")
    w2 = Signal(weights={"CooperateBot": 0.5, "TitForTatBot": 0.5})
    w3 = Signal.point_mass("TitForTatBot")
    plays = tuple(tau_play(matrix, "ConfidenceBot", 1.0, w) for w in (w1, w2, w3))
    assert plays == ("C", "D", "C")
    for actor in matrix.bots:
        if matrix.aggregator(actor) != "sum":
            continue
        for alpha in (0.0, 0.25, 0.5, 0.75, 1.0):
            assert tuple(tau_play(matrix, actor, alpha, w) for w in (w1, w2, w3)) != ("C", "D", "C"), (actor, alpha)


def test_native_needs_confidence_not_expectation(matrix) -> None:
    """The headline mechanism: under blur, ConfidenceBot vs τ(Dupoc). Both see the
    same channel; as the signal spreads, the native switches off first, because
    it needs one hypothesis to carry α on its own, not the cooperating mass as a
    whole."""
    channel = signal_family(matrix, t=0.3)
    row_native, row_lift = 0, 0
    for col in matrix.bots:
        out_native = tau_match(matrix, "ConfidenceBot", col, 0.6, channel)
        out_lift = tau_match(matrix, "DupocBot", col, 0.6, channel)
        row_native += out_native.row_action == "C"
        row_lift += out_lift.row_action == "C"
        # the native's decision mass never exceeds the lift's on the same signal
        assert out_native.row_coop_mass <= out_lift.row_coop_mass + 1e-12
    assert row_native <= row_lift


def test_native_never_reads_the_N_state() -> None:
    """A swept matrix never contains "N" for a native either: the clone copies
    Dupoc's cells, none of which is a proven `none`."""
    m = load_tau_matrix(bots=("MirrorBot", "ConfidenceBot", "DupocBot"), hypothetical_cells={})
    assert m.action("ConfidenceBot", "MirrorBot") == m.action("DupocBot", "MirrorBot") == "C"
    assert m.cell("MirrorBot", "MirrorBot").row_action == "N"

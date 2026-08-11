"""Def-3 vs Def-4 comparison: the control agrees, the separating zoo diverges.

The two headline facts locked in here are the whole point of the experiment:

1. On the milestone-1 control zoo the definitions are IDENTICAL at every
   (t, α) — and identical for a structural reason (equal bit-vectors), not by
   sampling luck. A regression that made them differ here would mean the Def-4
   arithmetic had drifted from the Lean semantics.
2. Adding EBot — one asymmetric base cell under a CONDITIONAL bot — makes them
   diverge. Without this test, fact 1 could be silently caused by a bug that
   collapses Def 4 into Def 3 (e.g. a probe geometry that never fires), and the
   experiment would report "no difference" for the wrong reason.
"""

from __future__ import annotations

import pytest

from pd_runner.tau.compare import (
    alpha_bands,
    asymmetry_report,
    def3_actions,
    def4_actions,
    sweep,
    verify_against_lean,
)
from pd_runner.tau.def4_theorems import TAU_THEOREMS_FILE, Def4Library
from pd_runner.tau.def4 import (
    CONTROL_BOTS,
    CONTROL_ZOO,
    SEPARATING_BOTS,
    SEPARATING_ZOO,
    Def4Bot,
    Probe,
    coop_mass_def4,
    probe_bit,
    tau_play_def4,
)
from pd_runner.tau.matrix import load_tau_matrix
from pd_runner.tau.signal import Signal


@pytest.fixture(scope="module")
def control_matrix():
    return load_tau_matrix(CONTROL_BOTS)


@pytest.fixture(scope="module")
def separating_matrix():
    return load_tau_matrix(SEPARATING_BOTS)


# ── The probe geometries ───────────────────────────────────────────────────


def test_constant_bots_are_alpha_independent(control_matrix):
    """Lean's TauCooperate/TauDefect are `.const`, so α never moves them.

    The α = 0 corner is the discriminating one: a self-probing bot with an
    all-zero bit-vector would COOPERATE there (mass 0 ≥ 0), which is what an
    earlier model did — and it contradicted the kernel.
    """
    sig = Signal({"CooperateBot": 0.5, "DefectBot": 0.5})
    for alpha in (0.0, 0.5, 1.0):
        assert (
            tau_play_def4(
                control_matrix, CONTROL_ZOO["DefectBot"], "DefectBot", alpha, sig
            )
            == "D"
        )
        assert (
            tau_play_def4(
                control_matrix, CONTROL_ZOO["CooperateBot"], "CooperateBot", alpha, sig
            )
            == "C"
        )


def test_constant_bot_rejects_a_missing_action():
    with pytest.raises(ValueError, match="action"):
        Def4Bot("X", Probe.CONSTANT)
    with pytest.raises(ValueError, match="action"):
        Def4Bot("X", Probe.SELF, action="C")


def test_self_probe_reads_the_actors_own_action(control_matrix):
    """SELF is Def 3's direction: 'what do I do against the hypothesis'."""
    bot = Def4Bot("X", Probe.SELF)
    # DupocBot defects against DefectBot, so its self-bit there is False.
    assert probe_bit(control_matrix, bot, "DupocBot", "DefectBot") is False
    assert probe_bit(control_matrix, bot, "DupocBot", "CooperateBot") is True


def test_reciprocity_probe_reads_the_hypothesis_action(separating_matrix):
    """RECIPROCITY reads the SAME cell from the other side — the Def-4 flip."""
    bot = Def4Bot("X", Probe.RECIPROCITY)
    # DupocBot vs EBot = (D, C): Dupoc defects, EBot cooperates.
    assert separating_matrix.action("DupocBot", "EBot") == "D"
    assert separating_matrix.action("EBot", "DupocBot") == "C"
    # So the two probes disagree on exactly this hypothesis.
    assert probe_bit(separating_matrix, bot, "DupocBot", "EBot") is True
    self_bot = Def4Bot("Y", Probe.SELF)
    assert probe_bit(separating_matrix, self_bot, "DupocBot", "EBot") is False


def test_third_party_probe_ignores_the_actor(control_matrix):
    """THIRD_PARTY measures the hypothesis against a fixed referent."""
    bot = Def4Bot("X", Probe.THIRD_PARTY, referent="CooperateBot")
    for actor in CONTROL_BOTS:
        assert probe_bit(control_matrix, bot, actor, "DefectBot") is (
            control_matrix.cooperates("DefectBot", "CooperateBot")
        )


def test_third_party_requires_a_referent():
    with pytest.raises(ValueError, match="referent"):
        Def4Bot("X", Probe.THIRD_PARTY)
    with pytest.raises(ValueError, match="referent"):
        Def4Bot("X", Probe.SELF, referent="CooperateBot")


# ── Threshold semantics ────────────────────────────────────────────────────


def test_threshold_is_ge_alpha_and_mass_is_a_sum(control_matrix):
    """`≥ α`, and the mass is the weighted sum of firing bits."""
    bot = CONTROL_ZOO["DupocBot"]
    signal = Signal({"CooperateBot": 0.25, "DefectBot": 0.75})
    # Reciprocity: does Coop cooperate with Dupoc? yes. Does Defect? no.
    mass = coop_mass_def4(control_matrix, bot, "DupocBot", signal)
    assert mass == pytest.approx(0.25)
    assert tau_play_def4(control_matrix, bot, "DupocBot", 0.25, signal) == "C"
    assert tau_play_def4(control_matrix, bot, "DupocBot", 0.26, signal) == "D"


def test_a_prefix_of_weights_suffices(control_matrix):
    """Cooperation needs SOME firing weight to cover θ, not all of it."""
    bot = CONTROL_ZOO["DupocBot"]
    signal = Signal({"CooperateBot": 0.6, "DefectBot": 0.4})
    # The Coop weight alone (0.6) already exceeds α = 0.5.
    assert tau_play_def4(control_matrix, bot, "DupocBot", 0.5, signal) == "C"


# ── Fact 1: the control zoo cannot separate the definitions ────────────────


def test_control_zoo_has_identical_bit_vectors(control_matrix):
    report = asymmetry_report(control_matrix, CONTROL_ZOO, CONTROL_BOTS)
    assert report.bit_divergences == ()
    assert not report.can_separate
    for _actor, d3, d4 in report.bit_vectors:
        assert d3 == d4


def test_control_zoo_asymmetry_does_not_bite(control_matrix):
    """It HAS asymmetric cells; they just sit under constant bots.

    This is the distinction the report exists to make: raw asymmetry is not
    sufficient for separation, so `can_separate` must not key off it.
    """
    report = asymmetry_report(control_matrix, CONTROL_ZOO, CONTROL_BOTS)
    assert report.asymmetric_pairs  # non-empty
    assert not report.can_separate  # yet cannot separate
    actors = {a for a, _h, _x, _y in report.asymmetric_pairs}
    assert actors <= {"CooperateBot", "DefectBot"}  # constants only


def test_control_zoo_matrices_agree_across_the_grid(control_matrix):
    """No PROBE divergence anywhere on the control zoo.

    The α = 0 constant-convention artifact is excluded deliberately (see
    `test_alpha_zero_divergences_are_flagged_as_a_convention_artifact`): it
    reflects Def 3 lifting DefectBot uniformly vs Lean's hand-written
    `.const .D`, not a difference in probe semantics.
    """
    comparisons, divergences = sweep(
        control_matrix, CONTROL_ZOO, CONTROL_BOTS, t_values=(0.0, 0.25, 0.5, 0.75, 1.0)
    )
    assert comparisons  # the sweep actually ran
    probe_divergences = [d for d in divergences if not d.constant_artifact]
    assert probe_divergences == []
    assert all(c.agrees for c in comparisons if c.alpha > 0.0)


# ── Fact 2: EBot separates them ────────────────────────────────────────────


def test_separating_zoo_flips_dupocs_ebot_bit(separating_matrix):
    report = asymmetry_report(separating_matrix, SEPARATING_ZOO, SEPARATING_BOTS)
    assert report.can_separate
    assert ("DupocBot", "EBot", False, True) in report.bit_divergences


def test_separating_zoo_matrices_diverge(separating_matrix):
    comparisons, divergences = sweep(
        separating_matrix, SEPARATING_ZOO, SEPARATING_BOTS, t_values=(0.0, 0.5, 1.0)
    )
    assert divergences, "EBot must make the definitions differ somewhere"
    # And the divergence is a real outcome difference, not just a mass shift.
    assert any(
        cell.def3 != cell.def4 for d in divergences for cell in d.cells
    )


def test_divergence_at_full_transparency_is_the_exploitation_cell(separating_matrix):
    """At t = 1 each side sees the truth, so the probe direction is exposed.

    Def 3's TauDupoc asks 'what do I do against EBot' → D. Def 4's asks 'what
    does EBot do against me' → C. The cell flips accordingly.
    """
    channel = {b: Signal.point_mass(b) for b in SEPARATING_BOTS}
    alpha = 1.0
    d3 = def3_actions(separating_matrix, "DupocBot", "EBot", alpha, channel)
    d4 = def4_actions(
        separating_matrix, SEPARATING_ZOO, "DupocBot", "EBot", alpha, channel
    )
    assert d3 != d4
    assert d3[0] == "D" and d4[0] == "C"


# ── The α axis ─────────────────────────────────────────────────────────────


def test_alpha_bands_cover_zero_and_above_the_top_mass():
    bands = alpha_bands([0.0, 0.5, 1.0])
    probes = [a for a, _lo, _hi in bands]
    assert 0.0 in probes
    assert 0.5 in probes and 1.0 in probes


def test_alpha_bands_add_a_probe_above_an_unreachable_top():
    """If no agent can reach mass 1, the all-defect band must still be probed."""
    bands = alpha_bands([0.0, 0.5])
    assert bands[-1][0] > 0.5
    assert bands[-1][2] == 1.0


# ── The Lean theorems are the ground truth ─────────────────────────────────


def test_every_def4_theorem_parses():
    """All 28 statements in Theorems/Tau/Matrix.lean must be readable.

    A silently-skipped theorem would shrink certified coverage without
    anyone noticing, which is exactly the failure mode this scanner exists to
    prevent.
    """
    lib = Def4Library.load()
    declared = len(
        [l for l in TAU_THEOREMS_FILE.read_text().splitlines()
         if l.startswith("theorem outcome_")]
    )
    assert len(lib.theorems) == declared
    assert declared >= 28


def test_theorem_regimes_are_classified():
    lib = Def4Library.load()
    regimes = {t.regime for t in lib.theorems}
    assert regimes == {"low", "high", "unconditional"}
    # The constants carry no θ hypothesis; the θ-bots carry both regimes.
    assert lib.regimes_for("TauDefect", "TauDefect") == ("unconditional",)
    assert set(lib.regimes_for("TauDupoc", "TauDupoc")) == {"low", "high"}


def test_lean_lookup_respects_the_alpha_regime():
    """The same matchup flips with θ — that IS the α-phase boundary."""
    lib = Def4Library.load()
    w = {"wC": 25, "wD": 25, "wTs": 25, "wTp": 0, "wL": 25}   # coop mass 75
    assert lib.cell("TauDupoc", "TauDupoc", 75, w) == ("C", "C")
    assert lib.cell("TauDupoc", "TauDupoc", 76, w) == ("D", "D")


def test_uncovered_cells_return_none_not_a_guess():
    lib = Def4Library.load()
    w = {"wC": 25, "wD": 25, "wTs": 25, "wTp": 0, "wL": 25}
    # No tau bot named TauEBot exists in Lean.
    assert lib.cell("TauEBot", "TauDupoc", 10, w) is None
    assert not lib.covers("TauEBot", "TauDupoc")


def test_control_model_agrees_with_the_kernel(control_matrix):
    """THE central check: the Python Def-4 model must match Lean everywhere.

    A conflict means `def4.py` has drifted from the certified semantics — the
    Python is wrong, not the kernel. This test caught three real bugs: constant
    bots modelled as probing bots, a reversed-orientation lookup, and a
    breakpoint that rounded above its own mass.
    """
    comparisons, _ = sweep(
        control_matrix,
        CONTROL_ZOO,
        CONTROL_BOTS,
        t_values=(0.0, 0.25, 0.5, 0.75, 1.0),
        library=Def4Library.load(),
    )
    ver = verify_against_lean(comparisons)
    assert ver.conflicts == (), f"model disagrees with Lean: {ver.conflicts}"
    assert ver.proven > 0, "no cells were actually checked against the kernel"


def test_separating_zoo_cells_are_honestly_uncertified(separating_matrix):
    """EBot has no Lean theorems, so its cells must read `predicted`.

    They must NOT be silently certified against a renormalized 4-bot signal —
    the theorems' guard lists have no slot for a fifth hypothesis, so a signal
    carrying EBot weight asks a question they cannot answer.
    """
    comparisons, _ = sweep(
        separating_matrix,
        SEPARATING_ZOO,
        SEPARATING_BOTS,
        t_values=(0.0, 0.5, 1.0),
        library=Def4Library.load(),
    )
    ver = verify_against_lean(comparisons)
    assert ver.conflicts == ()
    assert ver.predicted > 0
    assert ver.coverage < 1.0


def test_alpha_zero_divergences_are_flagged_as_a_convention_artifact(control_matrix):
    """The α = 0 constant difference must not be reported as a probe finding."""
    _comparisons, divergences = sweep(
        control_matrix, CONTROL_ZOO, CONTROL_BOTS, t_values=(0.0, 0.5, 1.0)
    )
    assert divergences, "the α=0 corner does differ"
    assert all(d.constant_artifact for d in divergences)
    assert all(d.alpha == 0.0 for d in divergences)

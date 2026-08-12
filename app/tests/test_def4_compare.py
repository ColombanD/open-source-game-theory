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
    """RECIPROCITY reads the SAME cell from the other side — but a PROVER probe
    is floor-aware: EBot's real cooperation is unprovable within budget."""
    # DupocBot vs EBot = (D, C): Dupoc defects, EBot cooperates.
    assert separating_matrix.action("DupocBot", "EBot") == "D"
    assert separating_matrix.action("EBot", "DupocBot") == "C"
    # A BEHAVIORAL reciprocity probe would see EBot's true cooperation…
    behavioral = Def4Bot("X", Probe.RECIPROCITY, prover=False)
    assert probe_bit(separating_matrix, behavioral, "DupocBot", "EBot") is True
    # …but a PROVER probe reads 0: the cooperation sits behind a failed
    # exploit-search, so its certificate pays the floor
    # (Lean: interp_probe_eOfSearch true + ps_probe_eOfSearch_false).
    prover = Def4Bot("X", Probe.RECIPROCITY)
    assert probe_bit(separating_matrix, prover, "DupocBot", "EBot") is False
    # On non-floor-blocked hypotheses the prover bit equals the true bit.
    assert probe_bit(separating_matrix, prover, "DupocBot", "CooperateBot") is True
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


def test_separating_zoo_diverges_on_ebots_own_row(separating_matrix):
    """The separation now lives in EBot's OWN row (the cascade), not in
    TauDupoc's EBot bit — that one is floor-blocked to 0, matching Def 3's 0
    (for a different reason: own-action-D vs unprovable-C)."""
    report = asymmetry_report(separating_matrix, SEPARATING_ZOO, SEPARATING_BOTS)
    assert report.can_separate
    # Def 3 reads EBot's self-cell (C → 1); the cascade's compound bit for the
    # EBot hypothesis is 0 (E(δ_E) fails its own reciprocity stage).
    assert ("EBot", "EBot", True, False) in report.bit_divergences
    # And TauDupoc's row NO LONGER diverges: both definitions give its EBot
    # hypothesis bit 0.
    assert not any(a == "DupocBot" for a, _h, _b3, _b4 in report.bit_divergences)


def test_separating_zoo_matrices_diverge(separating_matrix):
    comparisons, divergences = sweep(
        separating_matrix, SEPARATING_ZOO, SEPARATING_BOTS, t_values=(0.0, 0.5, 1.0)
    )
    assert divergences, "EBot must make the definitions differ somewhere"
    # And the divergence is a real outcome difference, not just a mass shift.
    assert any(
        cell.def3 != cell.def4 for d in divergences for cell in d.cells
    )


def test_divergence_at_full_transparency_is_ebots_self_play(separating_matrix):
    """At t = 1 each side sees the truth, and the definitions split on EBot
    itself: Def 3's lift reads EBot's self-cell (C) and cooperates; Def 4's
    cascade fails its own reciprocity stage (E(δ_C) defects) and defects at
    every α. The exploiter does not trust itself — faithfully."""
    channel = {b: Signal.point_mass(b) for b in SEPARATING_BOTS}
    for alpha in (0.5, 1.0):
        d3 = def3_actions(separating_matrix, "EBot", "EBot", alpha, channel)
        d4 = def4_actions(
            separating_matrix, SEPARATING_ZOO, "EBot", "EBot", alpha, channel
        )
        assert d3 == ("C", "C")
        assert d4 == ("D", "D")


def test_dupoc_vs_ebot_reproduces_the_base_floor_cell(separating_matrix):
    """At t = 1, α = 1, the Def-4 cell IS the base `(D, C)`: Dupoc cannot cite
    EBot's floor-priced cooperation (bit 0 → defect), while EBot's cascade
    passes its exploit stage and its reciprocity stage fires on Dupoc."""
    channel = {b: Signal.point_mass(b) for b in SEPARATING_BOTS}
    d4 = def4_actions(
        separating_matrix, SEPARATING_ZOO, "DupocBot", "EBot", 1.0, channel
    )
    assert d4 == ("D", "C")
    assert d4 == (
        separating_matrix.action("DupocBot", "EBot"),
        separating_matrix.action("EBot", "DupocBot"),
    )


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
    assert regimes == {"low", "high", "exploit", "window", "unconditional"}
    # The constants carry no θ hypothesis; the cooperators carry both regimes;
    # every TauEBot pair carries its three.
    assert lib.regimes_for("TauDefect", "TauDefect") == ("unconditional",)
    assert set(lib.regimes_for("TauDupoc", "TauDupoc")) == {"low", "high"}
    assert set(lib.regimes_for("TauEBot", "TauEBot")) == {"exploit", "window", "high"}


def test_every_matchup_covers_both_alpha_regimes():
    """Both sides of the α-boundary are proven for EVERY ordered pair.

    Milestone 1 originally proved the defect regime only on the diagonal, which
    left a quarter of the sweep uncertified at high α. The phase theorems always
    supported the full matrix; only the statements were missing.
    """
    lib = Def4Library.load()
    for row in lib.bots:
        for col in lib.bots:
            regimes = set(lib.regimes_for(row, col))
            assert regimes, f"{row} vs {col} has no theorem at all"
            if "TauEBot" in (row, col):
                covered = {"exploit", "window", "high"} <= regimes
            else:
                covered = regimes == {"unconditional"} or {"low", "high"} <= regimes
            assert covered, f"{row} vs {col} only covers {sorted(regimes)}"


def test_defect_regime_pairs_are_not_uniformly_DD():
    """Constants never flip, so a mixed cell has exactly one flipping side."""
    lib = Def4Library.load()
    w = {"wC": 25, "wD": 25, "wTs": 25, "wTp": 0, "wL": 25}
    high = 10**6  # far above any achievable mass
    assert lib.cell("TauDupoc", "TauCooperate", high, w) == ("D", "C")
    assert lib.cell("TauCooperate", "TauDupoc", high, w) == ("C", "D")
    assert lib.cell("TauDupoc", "TauTFTSim", high, w) == ("D", "D")


def test_lean_lookup_respects_the_alpha_regime():
    """The same matchup flips with θ — that IS the α-phase boundary."""
    lib = Def4Library.load()
    w = {"wC": 25, "wD": 25, "wTs": 25, "wTp": 0, "wL": 25}   # coop mass 75
    assert lib.cell("TauDupoc", "TauDupoc", 75, w) == ("C", "C")
    assert lib.cell("TauDupoc", "TauDupoc", 76, w) == ("D", "D")


def test_uncovered_cells_return_none_not_a_guess():
    lib = Def4Library.load()
    w = {"wC": 25, "wD": 25, "wTs": 25, "wTp": 0, "wL": 25}
    # A tau bot with no theorems at all yields no cell, rather than a guess.
    assert lib.cell("TauNonexistent", "TauDupoc", 10, w) is None
    assert not lib.covers("TauNonexistent", "TauDupoc")


def test_tau_ebot_is_in_the_library():
    """TauEBot is BUILT in Lean, so the separating bot is certified too."""
    lib = Def4Library.load()
    assert "TauEBot" in lib.bots
    assert lib.covers("TauEBot", "TauDupoc")
    assert set(lib.regimes_for("TauEBot", "TauDupoc")) == {"exploit", "window", "high"}


def test_the_theorems_partition_the_theta_axis():
    """For every pair, exactly ONE theorem applies at each (θ, w⃗) — the
    cascade refactor made the cooperators share one boundary (no mixed
    regimes remain) and gave TauEBot a three-regime partition."""
    lib = Def4Library.load()
    assert not any(t.regime in ("mixed_rc", "mixed_cr") for t in lib.theorems)
    w = {"wC": 10, "wD": 5, "wTs": 20, "wTp": 15, "wL": 10, "wE": 10}
    for row in lib.bots:
        for col in lib.bots:
            for theta in (0, 5, 10, 11, 30, 55, 56, 100):
                applying = [
                    t for t in lib.theorems
                    if (t.row, t.col) == (row, col) and t.applies(theta, w)
                ]
                assert len(applying) == 1, (
                    f"{row} vs {col} at θ={theta}: {[t.name for t in applying]}"
                )


def test_row_action_judges_by_the_actors_own_regime():
    """Each player's action is decided by ITS OWN signal, not a shared one.

    In a tournament the two sides see different blurs, so a lookup that
    evaluated both conditions against one weight vector would read the wrong
    theorem for mixed-boundary pairs.
    """
    lib = Def4Library.load()
    # TauDupoc facing an EBot point mass: the EBot bit is floor-blocked, so its
    # provable mass is 0 and it DEFECTS — the tau image of base
    # `DupocBot vs EBot = (D, C)`, read from Dupoc's side.
    w = {"wC": 0, "wD": 0, "wTs": 0, "wTp": 0, "wL": 0, "wE": 100}
    assert lib.row_action("TauDupoc", "TauEBot", 100, w) == "D"
    # TauEBot facing a Dupoc point mass: exploit mass 0 < θ ≤ reciprocity mass
    # 100 — the window — so it COOPERATES: the same base cell from EBot's side.
    w2 = {"wC": 0, "wD": 0, "wTs": 0, "wTp": 0, "wL": 100, "wE": 0}
    assert lib.row_action("TauEBot", "TauDupoc", 100, w2) == "C"


def test_tau_ebot_cooperation_is_a_window():
    """TauEBot defects at BOTH ends of the θ axis — the exploit stage fires
    below `wC`, the reciprocity mass runs out above `wC+wTs+wTp+wL`. No
    one-sided (Def-3-expressible) threshold has this shape."""
    lib = Def4Library.load()
    # exploit boundary wC = 10; window upper edge = 10+20+15+10 = 55.
    w = {"wC": 10, "wD": 5, "wTs": 20, "wTp": 15, "wL": 10, "wE": 10}
    assert lib.row_action("TauEBot", "TauCooperate", 10, w) == "D"  # exploits
    assert lib.row_action("TauEBot", "TauCooperate", 11, w) == "C"  # window
    assert lib.row_action("TauEBot", "TauCooperate", 55, w) == "C"  # window edge
    assert lib.row_action("TauEBot", "TauCooperate", 56, w) == "D"  # above
    # TauDupoc has no exploit stage: it cooperates all the way down to θ = 0.
    assert lib.row_action("TauDupoc", "TauCooperate", 10, w) == "C"
    assert lib.row_action("TauDupoc", "TauCooperate", 0, w) == "C"


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
    # Every control-zoo cell is covered, in both α regimes: a drop below 100%
    # means a theorem went missing or a regime stopped being reachable.
    assert ver.predicted == 0, "control zoo must be fully certified"
    assert ver.coverage == 1.0


def test_separating_zoo_cells_are_honestly_uncertified(separating_matrix):
    """The separating zoo is fully certified since the six-slot widening.

    Kept under its original name as the regression guard: if a future bot is
    modelled in Python before its Lean counterpart exists, or a guard list
    loses a hypothesis, coverage drops and this test says so.
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
    # The guard lists are SIX-slot now, so every bot votes over the whole zoo
    # and the separating comparison — the informative half — is fully certified.
    assert ver.predicted == 0
    assert ver.coverage == 1.0


def test_alpha_zero_divergences_are_flagged_as_a_convention_artifact(control_matrix):
    """The α = 0 constant difference must not be reported as a probe finding."""
    _comparisons, divergences = sweep(
        control_matrix, CONTROL_ZOO, CONTROL_BOTS, t_values=(0.0, 0.5, 1.0)
    )
    assert divergences, "the α=0 corner does differ"
    assert all(d.constant_artifact for d in divergences)
    assert all(d.alpha == 0.0 for d in divergences)

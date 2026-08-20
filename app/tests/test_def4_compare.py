"""Tests for the corrected Def-4 model (the source lift) and its coincidence
certification against Def 3.

The model under test is `def4.decide` — the Python twin of the Lean Spec-DSL
compiler — plus the three-check certification in `compare.py`. The expectations
below are the KERNEL's: the bit rows are transcribed from `Tau/VotePhases.lean`'s
`VoteBits` theorems, and the kernel check asserts the transcription stays honest.
"""

from __future__ import annotations

import pytest

from pd_runner.tau.compare import (
    WHITELIST,
    bit_coincidence,
    certify,
    kernel_check,
    phase_sweep,
)
from pd_runner.tau.def4 import (
    BASE_OF,
    CONTROL_BOTS,
    CONTROL_ZOO,
    FULL_BOTS,
    SEPARATING_BOTS,
    SEPARATING_ZOO,
    TEMPLATES,
    Decision,
    UnsupportedDiagonal,
    LiftSpec,
    Mode,
    SELF,
    Stage,
    decide,
    decision_table,
)
from pd_runner.tau.def4_theorems import TAU_ORDER, kernel_bits
from pd_runner.tau.matrix import load_tau_matrix


# ── the compound decisions (the Lean bit tables, transcribed) ──────────────────

EXPECTED_ACTIONS: dict[str, str] = {
    "TauCooperate": "CCCCCCCCCC",
    "TauDefect": "DDDDDDDDDD",
    "TauTFTSim": "CDCCCDCCCD",
    "TauTFTPf": "CDCCCDCCDD",
    "TauDupoc": "CDCCCDCDDD",
    "TauEBot": "DDCCCDCCCD",
    "TauJust": "CDCCCDCDDD",
    "TauOBot": "CDDDDDDDDD",
    "TauGuardian": "CDCCCDCCCD",
    "TauDBot": "DCCCCCCCCD",
}


def test_decision_table_matches_lean_bit_tables() -> None:
    table = decision_table()
    for A in TEMPLATES:
        got = "".join(table[A][T].action for T in TEMPLATES)
        assert got == EXPECTED_ACTIONS[A], f"{A}: {got} ≠ {EXPECTED_ACTIONS[A]}"


def test_kernel_check_passes() -> None:
    check = kernel_check()
    assert check.checked == 100
    assert check.passed, check.mismatches


def test_kernel_scanner_finds_all_rows() -> None:
    tables = kernel_bits()
    assert set(tables) == set(TAU_ORDER)


# ── the floor, structural ──────────────────────────────────────────────────────


def test_ebot_cooperations_floor_exactly_at_searcher_hypotheses() -> None:
    """Run-mode TauEBot (2026-08-19): a cooperation is floor-priced exactly when a
    WATCHED instance is itself a searcher whose play needs `search_f` — the floor
    moved one level down. Behavioral hypotheses (tftSim, obot) give cheap positive
    transcripts; prover hypotheses (tftPf, dupoc) and Guardian's punish-searcher
    stay true-but-unprovable."""
    for hyp in ("TauTFTSim", "TauOBot"):
        assert decide("TauEBot", hyp) == Decision("C", provable=True)
    for hyp in ("TauTFTPf", "TauDupoc", "TauGuardian"):
        assert decide("TauEBot", hyp) == Decision("C", provable=False)


def test_dupoc_reads_ebot_floor_as_zero() -> None:
    """τ(Dupoc)'s EBot entry: E(δ_L) cooperates, but no ≤k certificate exists, so
    Dupoc's prove-stage bit is 0 and its compound decision is D — the tau image of
    base `outcome_DupocBot_vs_EBot = (D, C)`."""
    assert decide("TauDupoc", "TauEBot") == Decision("D", provable=False)


def test_quine_diagonal_cooperates() -> None:
    """The Löb fixpoint: Dupoc at point mass on ITSELF fires (large k)."""
    assert decide("TauDupoc", "TauDupoc") == Decision("C", provable=True)


def test_shallow_cooperations_are_provable() -> None:
    assert decide("TauDupoc", "TauCooperate") == Decision("C", provable=True)
    assert decide("TauTFTPf", "TauCooperate") == Decision("C", provable=True)


def test_unsupported_diagonals_raise() -> None:
    zoo = {
        "Weird": LiftSpec((Stage(Mode.RUN, SELF, "C", "C"),), "D"),
    }
    with pytest.raises(UnsupportedDiagonal):
        decide("Weird", "Weird", zoo)
    anti = {
        "Anti": LiftSpec((Stage(Mode.PROVE, SELF, "C", "D"),), "C"),
    }
    with pytest.raises(UnsupportedDiagonal):
        decide("Anti", "Anti", anti)


def test_mutual_quine_wall_raises() -> None:
    """Two self-probers form the inexpressible 2-cycle; the model must refuse,
    not loop or guess — the Python shadow of the Lean termination discipline."""
    zoo = {
        "A": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
        "B": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
    }
    with pytest.raises(UnsupportedDiagonal):
        decide("A", "B", zoo)


# ── the coincidence certification ──────────────────────────────────────────────


def test_bit_coincidence_control() -> None:
    matrix = load_tau_matrix(CONTROL_BOTS)
    coin = bit_coincidence(matrix)
    assert coin.passed
    assert not coin.whitelisted_divergences  # EBot absent → whitelist unused


def test_bit_coincidence_separating() -> None:
    """35/36 agree; the ONE divergence is exactly the Mirror-truncation cell."""
    matrix = load_tau_matrix(SEPARATING_BOTS)
    coin = bit_coincidence(matrix)
    assert coin.passed, coin.unexpected
    div = coin.whitelisted_divergences
    assert len(div) == 1
    assert (div[0].template, div[0].hypothesis) == ("TauEBot", "TauEBot")
    assert div[0].def4 == "D" and div[0].def3 == "C"


def test_whitelist_is_exactly_the_two_recorded_cells() -> None:
    assert set(WHITELIST) == {("TauEBot", "TauEBot"), ("TauTFTPf", "TauGuardian")}


def test_bit_coincidence_full_zoo() -> None:
    """All 100 template cells against the total base matrix: 98 agree; the two
    divergences are exactly the whitelisted Mirror-truncation and prover-modality
    cells."""
    matrix = load_tau_matrix(FULL_BOTS)
    coin = bit_coincidence(matrix)
    assert len(coin.cells) == 100
    assert coin.passed, coin.unexpected
    div = {(c.template, c.hypothesis) for c in coin.whitelisted_divergences}
    assert div == {("TauEBot", "TauEBot"), ("TauTFTPf", "TauGuardian")}


def test_phase_sweep_control_attributed() -> None:
    matrix = load_tau_matrix(CONTROL_BOTS)
    sweep = phase_sweep(matrix, CONTROL_ZOO, CONTROL_BOTS, t_values=(0.0, 0.5, 1.0))
    assert sweep.passed, sweep.unexplained[:5]
    # every divergence is the α = 0 constant artifact (no EBot in this zoo)
    for c in sweep.divergent:
        assert c.alpha <= 1e-12


def test_phase_sweep_separating_attributed() -> None:
    """THE INVERSION: the zoo that 'separated' the definitions under the retracted
    reading certifies coincidence under the corrected one — every phase divergence
    vanishes when the whitelisted bit is patched, or is the α = 0 artifact."""
    matrix = load_tau_matrix(SEPARATING_BOTS)
    sweep = phase_sweep(
        matrix, SEPARATING_ZOO, SEPARATING_BOTS, t_values=(0.0, 0.5, 1.0)
    )
    assert sweep.passed, sweep.unexplained[:5]
    assert sweep.divergent  # the artifacts DO exist; they are just attributed


def test_certification_end_to_end() -> None:
    matrix = load_tau_matrix(SEPARATING_BOTS)
    cert = certify(
        matrix, SEPARATING_ZOO, SEPARATING_BOTS, "separating", t_values=(0.0, 1.0)
    )
    assert cert.passed


# ── conventions worth pinning ──────────────────────────────────────────────────


def test_constants_ignore_alpha() -> None:
    """TauDefect defects even at α = 0 (Lean `.const .D`), where Def 3's uniform
    lift would cooperate on mass 0 — the recorded α = 0 artifact."""
    from pd_runner.tau.signal import Signal
    from pd_runner.tau.def4 import tau_play_def4

    sig = Signal(weights={"CooperateBot": 1.0})
    assert tau_play_def4("TauDefect", 0.0, sig, CONTROL_ZOO) == "D"
    assert tau_play_def4("TauCooperate", 1.0, sig, CONTROL_ZOO) == "C"


def test_tft_variants_split_exactly_on_guardian() -> None:
    """HISTORY: on the 6-zoo this test asserted the two TFT lifts have IDENTICAL
    rows ("the prover/behavioral split is a budget gap, not an α gap"). That claim
    was zoo-relative, and Guardian falsifies it: its floor-priced cooperation is
    visible to the simulator and invisible to the prover — the ONE slot where the
    rows now differ, and only that one."""
    t = decision_table()
    for T in TEMPLATES:
        sim, pf = t["TauTFTSim"][T].action, t["TauTFTPf"][T].action
        if T == "TauGuardian":
            assert (sim, pf) == ("C", "D")
        else:
            assert sim == pf, T


def test_base_of_covers_templates() -> None:
    assert set(BASE_OF) == set(TEMPLATES)


# ── the 9-zoo additions (2026-08-18) ──────────────────────────────────────────


def test_guardian_cooperation_is_never_provable() -> None:
    """Guardian's C always sits behind its failed punish-search: every cooperative
    cell of its row is floor-priced — the third Gödelian phenomenon, and the reason
    the prover/behavioral split becomes an α-gap with Guardian in the zoo."""
    for T in TEMPLATES:
        d = decide("TauGuardian", T)
        if d.action == "C":
            assert not d.provable, T


def test_modality_split_on_guardian() -> None:
    """The two TFT lifts finally disagree at large k: the simulator sees Guardian's
    true cooperation, the prover cannot cite it."""
    assert decide("TauTFTSim", "TauGuardian").action == "C"
    assert decide("TauTFTPf", "TauGuardian").action == "D"


def test_just_rides_dupocs_column() -> None:
    """Norm-based and self-based reciprocity coincide on this zoo."""
    for T in TEMPLATES:
        assert decide("TauJust", T).action == decide("TauDupoc", T).action


def test_obot_cooperates_only_with_the_cooperator() -> None:
    for T in TEMPLATES:
        want = "C" if T == "TauCooperate" else "D"
        assert decide("TauOBot", T).action == want

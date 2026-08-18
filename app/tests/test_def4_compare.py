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
from pd_runner.tau.def4_theorems import ORDER6, kernel_bits
from pd_runner.tau.matrix import load_tau_matrix


# ── the compound decisions (the Lean bit tables, transcribed) ──────────────────

EXPECTED_ACTIONS: dict[str, str] = {
    "TauCooperate": "CCCCCC",
    "TauDefect": "DDDDDD",
    "TauTFTSim": "CDCCCD",
    "TauTFTPf": "CDCCCD",
    "TauDupoc": "CDCCCD",
    "TauEBot": "DDCCCD",
}


def test_decision_table_matches_lean_bit_tables() -> None:
    table = decision_table()
    for A in TEMPLATES:
        got = "".join(table[A][T].action for T in TEMPLATES)
        assert got == EXPECTED_ACTIONS[A], f"{A}: {got} ≠ {EXPECTED_ACTIONS[A]}"


def test_kernel_check_passes() -> None:
    check = kernel_check()
    assert check.checked == 36
    assert check.passed, check.mismatches


def test_kernel_scanner_finds_all_six_rows() -> None:
    tables = kernel_bits()
    assert set(tables) == set(ORDER6)


# ── the floor, structural ──────────────────────────────────────────────────────


def test_ebot_cooperations_are_floor_priced() -> None:
    """TauEBot's real cooperations sit behind its failed exploit probe, so they
    are TRUE but UNPROVABLE — the Gödelian pair, computed rather than stipulated."""
    for hyp in ("TauTFTSim", "TauTFTPf", "TauDupoc"):
        d = decide("TauEBot", hyp)
        assert d == Decision("C", provable=False)


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
        "Weird": LiftSpec((Stage(Mode.RUN, SELF, "C"),), "D"),
    }
    with pytest.raises(UnsupportedDiagonal):
        decide("Weird", "Weird", zoo)
    anti = {
        "Anti": LiftSpec((Stage(Mode.PROVE, SELF, "D"),), "C"),
    }
    with pytest.raises(UnsupportedDiagonal):
        decide("Anti", "Anti", anti)


def test_mutual_quine_wall_raises() -> None:
    """Two self-probers form the inexpressible 2-cycle; the model must refuse,
    not loop or guess — the Python shadow of the Lean termination discipline."""
    zoo = {
        "A": LiftSpec((Stage(Mode.PROVE, SELF, "C"),), "D"),
        "B": LiftSpec((Stage(Mode.PROVE, SELF, "C"),), "D"),
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


def test_whitelist_is_exactly_the_mirror_cell() -> None:
    assert set(WHITELIST) == {("TauEBot", "TauEBot")}


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


def test_tft_variants_coincide_at_large_k() -> None:
    """The prover/behavioral split is a BUDGET gap, not an α gap: at large k the
    two TFT lifts have identical bit rows."""
    t = decision_table()
    row_sim = [t["TauTFTSim"][T].action for T in TEMPLATES]
    row_pf = [t["TauTFTPf"][T].action for T in TEMPLATES]
    assert row_sim == row_pf


def test_base_of_covers_templates() -> None:
    assert set(BASE_OF) == set(TEMPLATES)

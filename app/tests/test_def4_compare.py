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
    EntangledCell,
    LiftSpec,
    Mode,
    SELF,
    Stage,
    decide,
    open_cells,
    decision_table,
)
from pd_runner.tau.def4_theorems import TAU_ORDER, kernel_bits
from pd_runner.tau.matrix import load_tau_matrix


# ── the compound decisions (the Lean bit tables, transcribed) ──────────────────

EXPECTED_ACTIONS: dict[str, str] = {
    "TauCooperate": "CCCCCCCCCCCCC",
    "TauDefect": "DDDDDDDDDDDDD",
    "TauTFTSim": "CDCCCDCCCDCCC",
    "TauTFTPf": "CDCCCDCCDDDDC",
    "TauDupoc": "CDCCCDCDDDDDC",
    "TauEBot": "DDCCCDCCCDDCC",
    "TauJust": "CDCCCDCDDDDDC",
    "TauOBot": "CDDDDDDDDDCDD",
    "TauGuardian": "CDCCCDCCCDCCC",
    "TauDBot": "DCCCCCCCCDDCC",
    "TauCupodTroll": "CCCCCCCCCCCCC",
    "TauCupod": "CDCCCCCCCCCDC",
    "TauCIMCIC": "CDCCCDCDDDDDC",
}


def test_decision_table_matches_lean_bit_tables() -> None:
    """TOTAL since the entangled closures (2026-08-21): every cell has a value, and
    the two entangled pairs carry the CLOSED values — Cupod×Dupoc by the floor
    (the tau image of the base red cell), CIMCIC×Dupoc by mutual bounded Löb
    (the tau image of base CIMCIC-vs-DupocBot `(C, C)`). Note τ(CIMCIC)'s row is
    IDENTICAL to τ(Dupoc)'s: the conditional cooperator and the Löbian cooperator
    behave the same on this zoo, through different mechanisms."""
    table = decision_table()
    for A in TEMPLATES:
        got = "".join(table[A][T].action for T in TEMPLATES)
        assert got == EXPECTED_ACTIONS[A], f"{A}: {got} ≠ {EXPECTED_ACTIONS[A]}"


def test_no_open_cells_and_six_entangled() -> None:
    """The `.sys` frontier is CLOSED: `open_cells` is empty, and the six entangled
    orientations (three self-prober pairs among dupoc/cupod/cimcic) are resolved by
    `_resolve_entangled` — floor for the anti-aligned pairs, mutual Löb for
    CIMCIC×Dupoc."""
    from pd_runner.tau.def4 import entangled_cells

    assert open_cells() == ()
    assert set(entangled_cells()) == {
        ("TauDupoc", "TauCupod"), ("TauCupod", "TauDupoc"),
        ("TauDupoc", "TauCIMCIC"), ("TauCIMCIC", "TauDupoc"),
        ("TauCupod", "TauCIMCIC"), ("TauCIMCIC", "TauCupod"),
    }


def test_entangled_closures_match_lean() -> None:
    """The six closed entangled cells, against their Lean theorems."""
    # Cupod×Dupoc — the floor (ps_probe_inst_cupod_dupoc_false etc.)
    assert decide("TauCupod", "TauDupoc") == Decision("C", provable=False)
    assert decide("TauDupoc", "TauCupod") == Decision("D", provable=False)
    # CIMCIC×Dupoc — mutual bounded Löb (cimcic_dupoc_plays_C / dupoc_cimcic_plays_C)
    assert decide("TauCIMCIC", "TauDupoc") == Decision("C", provable=True)
    assert decide("TauDupoc", "TauCIMCIC") == Decision("C", provable=True)
    # CIMCIC×Cupod — the floor again (cimcic_cupod_plays_D / cupod_cimcic_plays_C)
    assert decide("TauCIMCIC", "TauCupod") == Decision("D", provable=False)
    assert decide("TauCupod", "TauCIMCIC") == Decision("C", provable=False)


def test_kernel_check_passes() -> None:
    check = kernel_check()
    assert check.checked == 169
    assert check.passed, check.mismatches


def test_kernel_scanner_finds_all_rows() -> None:
    """All 13 rows are stated — and since the entangled closures, none carries an
    open-cell hypothesis (only Löb `∃k₂` gates)."""
    tables = kernel_bits()
    assert set(tables) == set(TAU_ORDER)


def test_kernel_check_has_no_unstated_rows() -> None:
    check = kernel_check()
    assert check.unstated == ()
    assert not check.mismatches


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


def test_mutual_quine_pair_resolves_by_alignment() -> None:
    """Two self-probers form a 2-cycle. HISTORY: before the `.sys` binder the model
    raised `UnsupportedDiagonal`; for one session after it, `EntangledCell` ("the
    answer does not exist"). Since the closures (2026-08-21 evening) the answer
    EXISTS: aligned cycles cooperate by mutual Löb, anti-aligned ones fall to the
    floor. Two Dupoc-clones align (each wants C, each fires C) → mutual `(C, C)`;
    a Dupoc-clone against a Cupod-clone anti-aligns → both play defaults,
    floor-priced."""
    aligned = {
        "A": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
        "B": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
    }
    assert decide("A", "B", aligned) == Decision("C", provable=True)
    anti = {
        "A": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
        "B": LiftSpec((Stage(Mode.PROVE, SELF, "D", "D"),), "C"),
    }
    assert decide("A", "B", anti) == Decision("D", provable=False)
    assert decide("B", "A", anti) == Decision("C", provable=False)


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


def test_whitelist_is_exactly_the_recorded_cells() -> None:
    assert set(WHITELIST) == {
        ("TauEBot", "TauEBot"),
        ("TauTFTPf", "TauGuardian"),
        ("TauTFTPf", "TauCupodTroll"),
        ("TauDupoc", "TauCupodTroll"),
        ("TauJust", "TauCupodTroll"),
    }


# Base CIMCIC↔OBot is the ONE unproven base pair the CIMCIC lift consults on the
# Def-3 side (the OBot two-watch census exists at the TAU shapes —
# `no_provable_twoTestD_cimcic_C` — but not yet at the base shapes). Same value the
# enlarged-zoo stipulations carry; drop when the base theorems land.
CIMCIC_OBOT_STIPULATION: dict[tuple[str, str], tuple[str, str]] = {
    ("CIMCIC", "OBot"): ("D", "D"),
}


def test_bit_coincidence_full_zoo() -> None:
    """All 144 template cells against the base matrix (total modulo the one
    stipulated CIMCIC↔OBot pair): the five whitelisted Mirror-truncation and
    prover-modality divergences remain the only ones — the entire CIMCIC row and
    column COINCIDE with the base cells, including the mutual-Löb DupocBot cell."""
    matrix = load_tau_matrix(FULL_BOTS, hypothetical_cells=CIMCIC_OBOT_STIPULATION)
    coin = bit_coincidence(matrix)
    assert len(coin.cells) == 144
    assert coin.passed, coin.unexpected
    div = {(c.template, c.hypothesis) for c in coin.whitelisted_divergences}
    assert div == {
        ("TauEBot", "TauEBot"),
        ("TauTFTPf", "TauGuardian"),
        ("TauTFTPf", "TauCupodTroll"),
        ("TauDupoc", "TauCupodTroll"),
        ("TauJust", "TauCupodTroll"),
    }


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


def test_tft_variants_split_exactly_on_the_floor_bots() -> None:
    """HISTORY: on the 6-zoo this asserted the two TFT lifts have IDENTICAL rows
    ("the prover/behavioral split is a budget gap, not an α gap"). Guardian
    falsified that (2026-08-19), and CupodTroll falsifies the follow-up claim that
    Guardian was the ONLY such slot (2026-08-20). The invariant that actually
    holds: the rows differ EXACTLY at the hypotheses whose cooperation is
    floor-priced — true but uncitable — and agree everywhere else."""
    t = decision_table()
    floor_bots = {"TauGuardian", "TauCupodTroll", "TauCupod"}
    for T in TEMPLATES:
        if T not in t["TauTFTSim"] or T not in t["TauTFTPf"]:
            continue  # open cell
        sim, pf = t["TauTFTSim"][T].action, t["TauTFTPf"][T].action
        if T in floor_bots:
            assert (sim, pf) == ("C", "D"), T
        else:
            assert sim == pf, T


def test_obot_cooperates_exactly_with_the_non_bullies() -> None:
    """OBot's two defection-watches must BOTH stay silent. On the 10-zoo only the
    unconditional cooperator passed; CupodTroll (2026-08-20) is the second — its
    identity check never fires, so it cooperates with everyone including the
    defector. The invariant is 'cooperates with whoever never defects on the
    canonical pair', not 'only with TauCooperate'."""
    want_C = {"TauCooperate", "TauCupodTroll"}
    for T in TEMPLATES:
        want = "C" if T in want_C else "D"
        assert decide("TauOBot", T).action == want, T
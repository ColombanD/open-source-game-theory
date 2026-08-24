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
    direct_kernel_vs_base,
    kernel_check,
    phase_sweep,
)
from pd_runner.tau.def4 import (
    BASE_OF,
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
    "TauCooperate": "CCCCCCCCCCCCCC",
    "TauDefect": "DDDDDDDDDDDDDD",
    "TauTFTSim": "CDCCCDCCCDCCCC",
    "TauTFTPf": "CDCCCDCCDDDDCD",
    "TauDupoc": "CDCCCDCDDDDDCD",
    "TauEBot": "DDCCCDCCCDDCCC",
    "TauJust": "CDCCCDCDDDDDCD",
    "TauOBot": "CDDDDDDDDDCDDD",
    "TauGuardian": "CDCCCDCCCDCCCC",
    "TauDBot": "DCCCCCCCCDDCCC",
    "TauCupodTroll": "CCCCCCCCCCCCCC",
    "TauCupod": "CDCCCCCCCCCDCD",
    "TauCIMCIC": "CDCCCDCDDDDDCD",
    # DIMCID's row: C wherever it cannot certify a defection. Identical to
    # TauCupod's — the suspicious cooperator and the conditional defector agree
    # on this zoo, by different mechanisms (a third coincidence of the kind
    # TauDupoc/TauCIMCIC already exhibit).
    "TauDIMCID": "CDCCCCCCCCCDCD",
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
    # four self-probers (dupoc, cupod, cimcic, dimcid) -> C(4,2)=6 pairs,
    # 12 ordered orientations
    sp = ("TauDupoc", "TauCupod", "TauCIMCIC", "TauDIMCID")
    assert set(entangled_cells()) == {
        (a, b) for a in sp for b in sp if a != b
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
    assert check.checked == 182
    assert check.passed, check.mismatches


def test_kernel_scanner_finds_all_rows_but_dimcid() -> None:
    """13 of the 14 rows are stated. `TauDIMCID`'s own `VoteBits` row is NOT: its
    off-cycle bits hit a POLARITY obstruction (its guard fires into `D`, so a
    provable guard falsifies its own antecedent and the soundness route CIMCIC
    used is unavailable) — see `Tau/Theorems/TauDIMCID/Helpers.lean`. Its COLUMN
    (what every other row plays against it) is fully proven, which is why the
    kernel check below still passes on 182 cells."""
    tables = kernel_bits()
    assert set(tables) == set(TAU_ORDER) - {"dimcid"}


def test_kernel_check_unstated_is_exactly_dimcid() -> None:
    """Zero MISMATCHES on 182 checked cells; the one unstated row is DIMCID's
    (see above). `unstated` and `mismatches` are deliberately different fields —
    "not yet proven" must never read as "disagrees"."""
    check = kernel_check()
    assert check.unstated == ("TauDIMCID",)
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


def test_kernel_agrees_with_base_directly() -> None:
    """**The end-to-end check, model-free.** `kernel_check` (model vs Lean) and
    `bit_coincidence` (model vs base) already compose to this, but composing two
    checks means a shared bug in the Python model could in principle cancel out.
    This one reads the bits straight out of Lean's `VoteBits` theorems and
    compares them to the base matrix, so a pass does not depend on the model.

    144 comparable cells (every template pair whose two base bots are in the
    zoo), 139 agree, and the 5 divergences are exactly the recorded
    whitelist — properties of the LIFT, not of any implementation."""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert len(d.cells) == 144
    assert d.passed, d.unexpected
    assert len(d.whitelisted_divergences) == 5
    # DIMCID's own row is not stated yet (its off-cycle bits are blocked); its
    # COLUMN is, which is why the count is still the full 144.
    assert d.missing_rows == ("TauDIMCID",)


def test_direct_and_composed_checks_agree() -> None:
    """The direct check and the model-mediated one must reach the same verdict on
    the same cells — if they ever diverge, the MODEL is wrong (the kernel and the
    base matrix are both machine-checked)."""
    m = load_tau_matrix(FULL_BOTS)
    direct = {(c.template, c.hypothesis): c.lean for c in direct_kernel_vs_base(m).cells}
    viamodel = {(c.template, c.hypothesis): c.def4 for c in bit_coincidence(m).cells}
    assert direct == viamodel


def test_whitelist_splits_into_two_distinct_causes() -> None:
    """The five whitelisted divergences are NOT one phenomenon, and the notes
    must not blur them (they did until 2026-08-21):

    * **budget staggering** — the base cell is a DAGGER cell, proven only under a
      side hypothesis granting one bot a bigger budget (enough to pay the
      partner's `search_f` floor). `tauZoo k` gives every bot the SAME `k`, so
      the stagger is unavailable by construction. Base and tau agree on the
      mathematics; they differ on the budget regime.
    * **genuine modality / coverage gaps** — the α-gap (a prover lift of a
      BEHAVIORAL base bot) and EBot's dropped Mirror branch.

    NOTE the two ways a base cell can be staggered, only ONE of which the matrix
    flags: `DupocBot × CupodTrollBot` carries an explicit side hypothesis (`hjk`)
    and so is a DAGGER cell, while `JustBot × CupodTrollBot` bakes the stagger
    into the statement itself (`JustBot (4*j+100)` vs `CupodTrollBot j`) and is
    therefore NOT flagged — `has_hypotheses` cannot see it. Same phenomenon,
    different bookkeeping; the test records both explicitly rather than relying
    on the dagger flag alone."""
    m = load_tau_matrix(FULL_BOTS)
    dagger = set(m.dagger_cells)

    # staggering, flagged by the matrix (explicit side hypothesis)
    assert (BASE_OF["TauDupoc"], BASE_OF["TauCupodTroll"]) in dagger
    # staggering, NOT flagged (the stagger lives in the theorem's statement)
    assert (BASE_OF["TauJust"], BASE_OF["TauCupodTroll"]) not in dagger
    staggering = {("TauDupoc", "TauCupodTroll"), ("TauJust", "TauCupodTroll")}

    # genuine modality / coverage gaps: same-budget base cells, no stagger
    modality = {("TauTFTPf", "TauGuardian"), ("TauTFTPf", "TauCupodTroll"),
                ("TauEBot", "TauEBot")}
    for A, T in modality:
        assert (BASE_OF[A], BASE_OF[T]) not in dagger, (A, T)

    assert staggering | modality == set(WHITELIST)


def test_whitelist_is_exactly_the_recorded_cells() -> None:
    assert set(WHITELIST) == {
        ("TauEBot", "TauEBot"),
        ("TauTFTPf", "TauGuardian"),
        ("TauTFTPf", "TauCupodTroll"),
        ("TauDupoc", "TauCupodTroll"),
        ("TauJust", "TauCupodTroll"),
    }


def test_bit_coincidence_full_zoo() -> None:
    """All 144 template cells against the TOTAL base matrix (the last unproven
    pair, CIMCIC↔OBot, became `outcome_CIMCIC_vs_OBot` on 2026-08-21): the five
    whitelisted Mirror-truncation and prover-modality divergences remain the only
    ones — the entire CIMCIC row and column COINCIDE with the base cells,
    including the mutual-Löb DupocBot cell."""
    matrix = load_tau_matrix(FULL_BOTS)
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
    # TauDIMCID joined the floor bots 2026-08-21: like Guardian's and Cupod's,
    # its cooperation is the ELSE-play of a failed search, so it is TRUE but
    # uncitable — the behavioral TFT counts it, the prover TFT cannot.
    floor_bots = {"TauGuardian", "TauCupodTroll", "TauCupod", "TauDIMCID"}
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
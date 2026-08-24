"""Tests for the Def-3 ≡ Def-4 certification, read straight from the kernel.

The Python spec-mirror (`tau/def4.py` — the `LiftSpec` cascade interpreter) was
REMOVED on 2026-08-24 along with the three model-mediated checks built on it
(`kernel_check`, `bit_coincidence`, `phase_sweep`). What remains is the check
that never depended on it: Lean's own `VoteBits` rows against the certified base
matrix. Every expectation below is therefore the KERNEL's, and the invariants
that used to be stated over modelled decisions are restated over the scanned bit
rows — same claims, one implementation instead of two.
"""

from __future__ import annotations

from pd_runner.tau.compare import (
    WHITELIST,
    certify,
    direct_kernel_vs_base,
)
from pd_runner.tau.def4_theorems import (
    BASE_OF,
    CONTROL_BOTS,
    LEAN_SLOT,
    SEPARATING_BOTS,
    TAU_ORDER,
    TEMPLATES,
    kernel_bits,
)
from pd_runner.tau.matrix import load_tau_matrix

FULL_BOTS: tuple[str, ...] = (
    "DupocBot", "CooperateBot", "DefectBot", "TitForTatBot", "EBot",
    "JustBot", "OBot", "GuardianBot", "DBot", "CupodTrollBot", "CIMCIC",
    "CupodBot", "DIMCID",
)
"""The base bots the full certification runs over (TitForTatBot carries both TFT
lift variants, so 13 base bots cover 14 templates).

CupodBot and DIMCID were MISSING here until 2026-08-24, even though their base
cells landed on 08-21 — so the check silently ran on 144 of the 182 comparable
cells and reported green while four cells diverged unexamined. Keep this list in
sync with the base bots that have proven cells, or the certification understates
its own coverage."""


# ── the kernel bit tables ──────────────────────────────────────────────────────


def test_kernel_scanner_finds_all_rows_but_dimcid() -> None:
    """13 of the 14 rows are stated. `TauDIMCID`'s own `VoteBits` row is NOT: its
    off-cycle bits hit a POLARITY obstruction (its guard fires into `D`, so a
    provable guard falsifies its own antecedent and the soundness route CIMCIC
    used is unavailable) — see `Tau/Theorems/TauDIMCID/Helpers.lean`. Its COLUMN
    (what every other row plays against it) is fully proven."""
    tables = kernel_bits()
    assert set(tables) == set(TAU_ORDER) - {"dimcid"}


def test_every_stated_row_is_complete() -> None:
    """A stated row carries a bit for every slot in `tauOrder` — the scanner
    raises on a short row, so this pins that it stays that way."""
    for tmpl, row in kernel_bits().items():
        assert set(row) == set(TAU_ORDER), tmpl


# ── the certification ──────────────────────────────────────────────────────────


def test_kernel_agrees_with_base_directly() -> None:
    """**The end-to-end check, model-free.** The bits come straight out of Lean's
    `VoteBits` theorems and the cells out of the certified base matrix, so a pass
    depends on no Python model at all.

    182 comparable cells (every template pair whose two base bots are in the
    zoo), 175 agree, and the 7 divergences are exactly the recorded whitelist —
    properties of the LIFT, not of any implementation.

    Was 144/139/5 until 2026-08-24, when CupodBot and DIMCID were added to
    `FULL_BOTS`: their base cells had landed on 08-21 but the list was never
    updated, so 38 comparable cells went unchecked and four divergences sat
    unexamined behind a green result."""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert len(d.cells) == 182
    assert d.passed, d.unexpected
    assert d.agreements == 175
    assert len(d.whitelisted_divergences) == 7
    # DIMCID's own row is not stated yet (its off-cycle bits are blocked); its
    # COLUMN is, which is why the count is still the full 144.
    assert d.missing_rows == ("TauDIMCID",)


def test_certification_end_to_end() -> None:
    cert = certify(load_tau_matrix(SEPARATING_BOTS), "separating")
    assert cert.passed


def test_control_zoo_certifies() -> None:
    cert = certify(load_tau_matrix(CONTROL_BOTS), "control")
    assert cert.passed


def test_missing_rows_are_reported_not_guessed() -> None:
    """An unstated row must be REPORTED, never predicted: absence is the honest
    signal that a bit is unproven. This is the property the removal of the Python
    model bought — the model would have supplied a DIMCID row from its own
    arithmetic, with nothing to check it against."""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert "TauDIMCID" in d.missing_rows
    assert all(c.template != "TauDIMCID" for c in d.cells)


# ── the whitelist ──────────────────────────────────────────────────────────────


def test_whitelist_is_exactly_the_recorded_cells() -> None:
    assert set(WHITELIST) == {
        # coverage: the lift cannot express the base bot's guard
        ("TauEBot", "TauEBot"),
        # prover-modality floors (the α-gap), one per floor bot
        ("TauTFTPf", "TauGuardian"),
        ("TauTFTPf", "TauCupodTroll"),
        ("TauTFTPf", "TauCupod"),
        ("TauTFTPf", "TauDIMCID"),
        # budget staggering
        ("TauDupoc", "TauCupodTroll"),
        ("TauJust", "TauCupodTroll"),
    }


def test_whitelist_splits_into_three_distinct_causes() -> None:
    """The whitelisted divergences are NOT one phenomenon, and the notes must not
    blur them (they did until 2026-08-21, when two were miscategorised):

    * **budget staggering** — the base cell is a DAGGER cell, proven only under a
      side hypothesis (or a stagger baked into the statement) granting one bot a
      bigger budget, enough to pay the partner's `search_f` floor. `tauZoo k`
      gives every bot the SAME `k`, so the stagger is unavailable by
      construction. Base and tau agree on the mathematics and differ on the
      budget regime.
    * **prover-modality floors** — the α-gap proper: a PROVER lift of a
      BEHAVIORAL base bot, facing a partner whose cooperation is true but
      floor-priced. One entry per floor bot (Guardian, CupodTroll, Cupod,
      DIMCID).
    * **coverage / guard-target truncation** — the lift cannot express the base
      bot's guard at all: EBot's dropped Mirror branch, and CupodTroll's identity
      guard, which names a BARE bot in base but an INSTANCE in the lift and so
      can never fire.

    Only the middle group is evidence for the α-gap; conflating the others would
    overstate it."""
    m = load_tau_matrix(FULL_BOTS)
    dagger = set(m.dagger_cells)

    staggering = {("TauDupoc", "TauCupodTroll"), ("TauJust", "TauCupodTroll")}
    for A, T in staggering:
        assert (BASE_OF[A], BASE_OF[T]) in dagger, (A, T)

    modality = {("TauTFTPf", "TauGuardian"), ("TauTFTPf", "TauCupodTroll"),
                ("TauTFTPf", "TauCupod"), ("TauTFTPf", "TauDIMCID")}
    coverage = {("TauEBot", "TauEBot")}
    # the prover-floor cells are never budget artifacts
    for A, T in modality:
        assert (BASE_OF[A], BASE_OF[T]) not in dagger, (A, T)
    assert (BASE_OF["TauEBot"], BASE_OF["TauEBot"]) not in dagger

    # every prover-floor entry is the PROVER TFT — that is what makes it the α-gap
    assert all(A == "TauTFTPf" for A, _ in modality)

    assert staggering | modality | coverage == set(WHITELIST)


def test_every_whitelisted_cell_actually_diverges() -> None:
    """The whitelist must not accumulate cells that have since been repaired — a
    stale entry would silently excuse a future regression at that cell."""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    diverging = {(c.template, c.hypothesis) for c in d.whitelisted_divergences}
    assert diverging == set(WHITELIST)


# ── invariants over the kernel rows ────────────────────────────────────────────


def _row(tables: dict[str, dict[str, str]], template: str) -> dict[str, str]:
    """A stated kernel row, keyed by TEMPLATE name rather than Lean slot."""
    slot_row = tables[LEAN_SLOT[template]]
    return {T: slot_row[LEAN_SLOT[T]] for T in TEMPLATES}


def test_tft_variants_split_exactly_on_the_floor_bots() -> None:
    """HISTORY: on the 6-zoo this asserted the two TFT lifts have IDENTICAL rows
    ("the prover/behavioral split is a budget gap, not an α gap"). Guardian
    falsified that (2026-08-19), and CupodTroll falsifies the follow-up claim that
    Guardian was the ONLY such slot (2026-08-20). The invariant that actually
    holds: the rows differ EXACTLY at the hypotheses whose cooperation is
    floor-priced — true but uncitable — and agree everywhere else.

    Now read off the KERNEL rows instead of the deleted model's decision table."""
    tables = kernel_bits()
    sim_row, pf_row = _row(tables, "TauTFTSim"), _row(tables, "TauTFTPf")
    # TauDIMCID joined the floor bots 2026-08-21: like Guardian's and Cupod's,
    # its cooperation is the ELSE-play of a failed search, so it is TRUE but
    # uncitable — the behavioral TFT counts it, the prover TFT cannot.
    floor_bots = {"TauGuardian", "TauCupodTroll", "TauCupod", "TauDIMCID"}
    for T in TEMPLATES:
        if T in floor_bots:
            assert (sim_row[T], pf_row[T]) == ("C", "D"), T
        else:
            assert sim_row[T] == pf_row[T], T


def test_obot_cooperates_exactly_with_the_non_bullies() -> None:
    """OBot's two defection-watches must BOTH stay silent. On the 10-zoo only the
    unconditional cooperator passed; CupodTroll (2026-08-20) is the second — its
    identity check never fires, so it cooperates with everyone including the
    defector. The invariant is 'cooperates with whoever never defects on the
    canonical pair', not 'only with TauCooperate'."""
    row = _row(kernel_bits(), "TauOBot")
    want_C = {"TauCooperate", "TauCupodTroll"}
    for T in TEMPLATES:
        assert row[T] == ("C" if T in want_C else "D"), T


def test_constant_rows_are_constant() -> None:
    """The two `.const` templates play their action against every hypothesis."""
    tables = kernel_bits()
    assert set(_row(tables, "TauCooperate").values()) == {"C"}
    assert set(_row(tables, "TauDefect").values()) == {"D"}

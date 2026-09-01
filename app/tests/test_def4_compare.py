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
    "CupodBot", "DIMCID", "PrudentBot", "MirrorBot",
)
"""The base bots the full certification runs over (TitForTatBot carries both TFT
lift variants and DupocBot also carries the NATIVE TauMaxConfidence — whose
hypothesis-role instance IS Dupoc's — so 15 base bots cover 17 templates).

MirrorBot joined on 2026-08-24 evening, once τ(Mirror) had a stated row: its
proven-`none` self-play loads as the fifth state "N", and the kernel reports
τ(Mirror)'s divergent diagonal the same way, so that cell compares N = N.

CupodBot and DIMCID were MISSING here until 2026-08-24, even though their base
cells landed on 08-21 — so the check silently ran on 144 of the 182 comparable
cells and reported green while four cells diverged unexamined. Keep this list in
sync with the base bots that have proven cells, or the certification understates
its own coverage."""


# ── the kernel bit tables ──────────────────────────────────────────────────────


def test_kernel_scanner_finds_all_rows() -> None:
    """ALL rows are stated (15 on 2026-08-25; 17 since 08-27 with the native
    MaxConfidenceBot's slot). τ(Mirror)'s is a PREFIX row
    over `tauOrderInit` (its diagonal diverges; the scanner records that slot as
    "N"). τ(DIMCID)'s — the last to land — needed the provability-tracking tower
    census (`Base/TowerCensus.lean`) for its two then-D searcher partners."""
    tables = kernel_bits()
    assert set(tables) == set(TAU_ORDER)
    assert tables["mirror"]["mirror"] == "N"


def test_every_stated_row_is_complete() -> None:
    """A stated row carries a bit for every slot in `tauOrder` — the scanner
    raises on a short row, so this pins that it stays that way."""
    for tmpl, row in kernel_bits().items():
        assert set(row) == set(TAU_ORDER), tmpl


# ── the certification ──────────────────────────────────────────────────────────


def test_kernel_agrees_with_base_directly() -> None:
    """**The end-to-end check, model-free.** The bits come straight out of Lean's
    `RowSpec` rows and the cells out of the certified base matrix, so a pass
    depends on no Python model at all.

    289 comparable cells — the 17×17 matrix without TauTFTPf — ALL agree; the
    whitelist is empty. The two NATIVE templates (TauMaxConfidence, TauMinConfidence)
    are both compared against DupocBot: each one's whole row AND column must equal
    Dupoc's base cells, which is the kernel-certified form of the matrix CLONE the
    `body+natives` zoo uses. (History: 144/139/5 until 2026-08-24 when CupodBot and
    DIMCID joined `FULL_BOTS` — 38 cells had gone unchecked behind a green result;
    210/204/6, then 225/219/6 on 08-25 with τ(DIMCID)'s row and TauTFTPf dropped;
    225/225/0 on 08-27 when the four staggered base cells were replaced by their
    shared-budget values and the staggered results became `*_staggered` non-cell
    theorems; 256/256/0 later that day with MaxConfidenceBot's slot; 289/289/0 on
    2026-09-01 with MinConfidenceBot's.)"""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert len(d.cells) == 289
    assert d.passed, d.unexpected
    assert d.agreements == 289
    assert len(d.whitelisted_divergences) == 0
    assert d.missing_rows == ()


def test_staggered_results_survive_as_non_cell_theorems() -> None:
    """The four cooperative results at a budget stagger are still theorems in the
    library — renamed `*_staggered`, untagged, outside the census — while their
    shared-budget values fill the cells. Nothing named `_samek` remains."""
    import re
    from pathlib import Path

    theorems = Path(__file__).resolve().parents[2] / "engine" / "PrisonersDilemma" / "Theorems"
    declared: set[str] = set()
    for f in theorems.rglob("*.lean"):
        declared |= set(re.findall(r"^theorem (outcome_\w+)\b", f.read_text(), re.M))
    assert {
        "outcome_PrudentBot_vs_DupocBot_staggered",
        "outcome_JustBot_vs_PrudentBot_staggered",
        "outcome_JustBot_vs_CupodTrollBot_staggered",
        "outcome_CupodTrollBot_vs_DupocBot_staggered",
    } <= declared
    assert not [n for n in declared if n.endswith("_samek")]


def test_tftpf_is_not_certified_against_base() -> None:
    """TauTFTPf is the prover reading of TitForTatBot's question — a tau-only
    variant with no base bot. It has a kernel row (the α-gap tests read it) but
    must appear in no base comparison, as row or as hypothesis."""
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert all(c.template != "TauTFTPf" and c.hypothesis != "TauTFTPf" for c in d.cells)
    assert "TauTFTPf" not in d.missing_rows
    assert "TauTFTPf" not in BASE_OF


def test_certification_end_to_end() -> None:
    cert = certify(load_tau_matrix(SEPARATING_BOTS), "separating")
    assert cert.passed


def test_control_zoo_certifies() -> None:
    cert = certify(load_tau_matrix(CONTROL_BOTS), "control")
    assert cert.passed


def test_missing_rows_are_reported_not_guessed(monkeypatch) -> None:
    """An unstated row must be REPORTED, never predicted: absence is the honest
    signal that a bit is unproven. This is the property the removal of the Python
    model bought — the model would have supplied a row from its own arithmetic,
    with nothing to check it against. Every row is stated now, so the property is
    exercised on a kernel table with DIMCID's row withheld."""
    from pd_runner.tau import compare as compare_mod
    full = kernel_bits()
    withheld = {k: v for k, v in full.items() if k != "dimcid"}
    monkeypatch.setattr(compare_mod, "kernel_bits", lambda: withheld)
    d = direct_kernel_vs_base(load_tau_matrix(FULL_BOTS))
    assert "TauDIMCID" in d.missing_rows
    assert all(c.template != "TauDIMCID" for c in d.cells)


# ── the whitelist ──────────────────────────────────────────────────────────────


def test_whitelist_is_empty() -> None:
    """No recorded divergence remains: base cells are shared-budget values (08-27)."""
    assert WHITELIST == {}


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
      floor-priced. Empty since 2026-08-25: TauTFTPf has no base bot, so it is
      compared nowhere (`test_tftpf_is_not_certified_against_base`).
    * **coverage / guard-target truncation** — the lift cannot express the base
      bot's guard at all: EBot's dropped Mirror branch, and CupodTroll's identity
      guard, which names a BARE bot in base but an INSTANCE in the lift and so
      can never fire.

    Only the middle group is evidence for the α-gap; conflating the others would
    overstate it."""
    m = load_tau_matrix(FULL_BOTS)
    dagger = set(m.dagger_cells)

    # budget staggering: EMPTY since 2026-08-27 — the six former entries are now
    # shared-budget base cells (`*_staggered` companions hold the cooperative
    # results), so they are neither daggers nor divergences any more
    former_staggering = {("TauDupoc", "TauCupodTroll"), ("TauJust", "TauCupodTroll"),
                         ("TauPrudent", "TauDupoc"), ("TauDupoc", "TauPrudent"),
                         ("TauPrudent", "TauJust"), ("TauJust", "TauPrudent")}
    for A, T in former_staggering:
        assert (BASE_OF[A], BASE_OF[T]) not in dagger, (A, T)

    # prover-modality floors: EMPTY since 2026-08-25 — TauTFTPf, the only prover
    # variant of a behavioral base bot, has no base row and is compared nowhere
    modality: set[tuple[str, str]] = set()
    coverage: set[tuple[str, str]] = set()   # empty since 2026-08-24
    # the prover-floor cells are never budget artifacts
    for A, T in modality:
        assert (BASE_OF[A], BASE_OF[T]) not in dagger, (A, T)
    assert not coverage

    # every prover-floor entry is the PROVER TFT — that is what makes it the α-gap
    assert all(A == "TauTFTPf" for A, _ in modality)

    assert modality | coverage == set(WHITELIST) == set()


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


# ── The Def-4 substrate (2026-09-01): the matrix PLAYS from the kernel rows ────


def test_paper_zoos_are_kernel_backed() -> None:
    """Every member of the three paper zoos (and critch8) plays from its own
    kernel-proven RowSpec row — `test_bit`/`cooperates` read `kernel_rows`, not
    the base cells, and the load verified the two agree."""
    from pd_runner.tau.matrix import ZOOS

    for key in ("body", "body+twins", "body+natives", "critch8"):
        m = ZOOS[key].load()
        assert m.is_kernel_backed, key
        assert set(m.kernel_backed_bots) == set(m.bots), key


def test_replay_zoo_is_not_kernel_backed() -> None:
    """`apply_contradictions` drops the kernel rows: a knowingly-wrong replay
    matrix must play from its contradicted cells, and its provenance must say
    so. Its test bits follow the contradictions, not the kernel."""
    from pd_runner.tau.matrix import ZOOS

    m = ZOOS["superficial-standalone"].load()
    assert not m.is_kernel_backed
    assert m.kernel_backed_bots == ()
    # the DBot/DupocBot cell is one the CSV got wrong: (C, C) there, (C, D) proven
    assert m.test_bit("DupocBot", "DBot") == "C"      # the contradicted value…
    certified = ZOOS["critch8"].load()
    assert certified.test_bit("DupocBot", "DBot") == "D"  # …not the kernel's


def test_templateless_bot_degrades_without_lying() -> None:
    """A roster holding a bot with no tau template still loads (base-cell
    fallback) but reports itself not kernel-backed."""
    from pd_runner.tau.matrix import load_tau_matrix

    m = load_tau_matrix(bots=("CooperateBot", "DefectBot", "WaryBot"),
                        hypothetical_cells={})
    assert not m.is_kernel_backed
    assert m.cooperates("CooperateBot", "WaryBot")  # base cell still answers


def test_kernel_base_mismatch_raises() -> None:
    """A present-but-stale export must fail the load loudly, never silently pick
    a side: flip one proven base cell and the guard names the pair."""
    import dataclasses

    import pytest

    from pd_runner.tau.matrix import PAPER_BODY_SUB_ZOO, _kernel_rows_for, load_tau_matrix

    m = load_tau_matrix(PAPER_BODY_SUB_ZOO, hypothetical_cells={})
    doctored = dict(m._cells)
    key = ("DupocBot", "DefectBot")   # proven (D, C); pretend the theorem said C
    doctored[key] = dataclasses.replace(doctored[key], row_action="C")
    with pytest.raises(ValueError, match="DupocBot vs DefectBot"):
        _kernel_rows_for(PAPER_BODY_SUB_ZOO, doctored)

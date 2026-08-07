"""Tests for the tau (graded transparency) layer.

The load-bearing one is `test_anchor_theorem_*`: Def 3 was chosen over Def 2
precisely because the tau lift reproduces the base outcome matrix at full
transparency. If that breaks, the construction is not a lift of A.
"""

from __future__ import annotations

import math

import pytest

from pd_runner.tau.matrix import (
    CERTIFIED_SUB_ZOO,
    CUPOD_STIPULATIONS,
    DEFAULT_ZOO,
    ENLARGED_STIPULATIONS,
    ENLARGED_SUB_ZOO,
    FULL_CERTIFIED_SUB_ZOO,
    PROVEN_ONLY_SUB_ZOO,
    ZOOS,
    get_zoo,
    load_tau_matrix,
    maximum_certified_sub_zoo,
)
from pd_runner.tau.play import (
    alpha_breakpoints,
    coop_mass,
    exact_alpha_breakpoints,
    tau_match,
    tau_play,
)
from pd_runner.tau.signal import (
    Signal,
    behavioral_distance_matrix,
    behavioral_twins,
    signal_family,
    softmax_signal,
    temperature_for_transparency,
    transparency,
)
from pd_runner.tau.sweep import (
    anchor_holds,
    base_tournament_cells,
    run_tournament,
)


@pytest.fixture(scope="module")
def matrix():
    return load_tau_matrix()


# ---------------------------------------------------------------- matrix ----

def test_sub_zoo_is_totally_proven(matrix) -> None:
    """Every ordered cell resolves — the tau layer is a total function."""
    assert len(matrix) == len(CERTIFIED_SUB_ZOO)
    for row in matrix.bots:
        for col in matrix.bots:
            cell = matrix.cell(row, col)
            assert cell.row_action in ("C", "D")
            assert cell.col_action in ("C", "D")


def test_certified_sub_zoo_is_still_maximal() -> None:
    """Guards against the constant going stale as new cells get proven.

    Not a correctness failure if it drifts — a prompt to re-run
    `python -m pd_runner.tau.matrix --recompute` and widen the zoo.
    """
    assert set(maximum_certified_sub_zoo()) >= set(FULL_CERTIFIED_SUB_ZOO)


def test_default_zoo_composition() -> None:
    """LegibleBot/JustBot out (twins), CupodBot in (twin-breaker)."""
    assert set(CERTIFIED_SUB_ZOO) == (
        set(FULL_CERTIFIED_SUB_ZOO) - {"LegibleBot", "JustBot"}
    ) | {"CupodBot"}
    assert "CupodTrollBot" in CERTIFIED_SUB_ZOO
    # The full zoo is still totally proven — the exclusions are about twins.
    assert load_tau_matrix(bots=FULL_CERTIFIED_SUB_ZOO).is_fully_proven


def test_default_zoo_is_conditional_on_stipulations() -> None:
    """CupodBot enters via two STIPULATED cells; that must stay visible."""
    m = load_tau_matrix()
    assert not m.is_fully_proven
    # Each stipulated pair contributes its cell and its transpose.
    assert len(m.hypothetical_cells) == 2 * len(CUPOD_STIPULATIONS)
    assert m.cell("CupodBot", "DupocBot").hypothetical
    assert m.cell("PrudentBot", "CupodBot").hypothetical
    # Everything else is kernel-backed.
    assert not m.cell("CupodTrollBot", "CupodBot").hypothetical


def test_proven_only_zoo_needs_no_stipulations() -> None:
    """The kernel-only fallback, for results that must not rest on a what-if."""
    m = load_tau_matrix(bots=PROVEN_ONLY_SUB_ZOO)
    assert m.is_fully_proven
    assert "CupodBot" not in m.bots


def test_default_zoo_requires_its_stipulations() -> None:
    """Opting out (`{}`) must fail loudly, never silently pick a convention."""
    with pytest.raises(ValueError, match="not total"):
        load_tau_matrix(hypothetical_cells={})


def test_orientation_is_respected(matrix) -> None:
    """Asymmetric cells must not be silently transposed.

    DBot vs CupodTrollBot is (D, C): orientation is load-bearing, which is why
    the tau layer reads theorems directly rather than the triangular render.
    """
    assert matrix.action("DBot", "CupodTrollBot") == "D"
    assert matrix.action("CupodTrollBot", "DBot") == "C"


def test_reversed_cells_agree(matrix) -> None:
    """outcome(A,B) = (a,b) iff outcome(B,A) = (b,a), for every pair."""
    for row in matrix.bots:
        for col in matrix.bots:
            fwd, rev = matrix.cell(row, col), matrix.cell(col, row)
            assert fwd.row_action == rev.col_action
            assert fwd.col_action == rev.row_action


def test_unproven_bot_is_rejected(matrix) -> None:
    """A hole must fail loudly, not fall back to an unchosen convention."""
    with pytest.raises(ValueError, match="not total"):
        load_tau_matrix(bots=CERTIFIED_SUB_ZOO + ("OptimBot",))


def test_proven_none_loads_as_fifth_state() -> None:
    """MirrorBot self-play is proven `none` and loads as the "N" cell."""
    assert "MirrorBot" not in CERTIFIED_SUB_ZOO  # predates the fifth state
    m = load_tau_matrix(bots=("CooperateBot", "MirrorBot"), hypothetical_cells={})
    cell = m.cell("MirrorBot", "MirrorBot")
    assert (cell.row_action, cell.col_action) == ("N", "N")
    assert cell.shape == "no_outcome"
    assert not cell.hypothetical
    assert m.is_fully_proven
    # Pessimistic reading downstream: "N" is not cooperation.
    assert not m.cooperates("MirrorBot", "MirrorBot")


def test_stipulation_cannot_shadow_a_proven_none() -> None:
    """The "N" state is kernel-backed — a what-if cell may not replace it."""
    with pytest.raises(ValueError, match="proven"):
        load_tau_matrix(
            bots=("CooperateBot", "MirrorBot"),
            hypothetical_cells={("MirrorBot", "MirrorBot"): ("C", "C")},
        )


def test_enlarged_zoo_loads_and_is_conditional() -> None:
    """The 16-bot zoo is total under its stipulations, and says so."""
    m = load_tau_matrix(ENLARGED_SUB_ZOO, hypothetical_cells=ENLARGED_STIPULATIONS)
    assert len(m) == 16
    assert not m.is_fully_proven
    # Each stipulated pair contributes its cell and its transpose.
    assert len(m.hypothetical_cells) == 2 * len(ENLARGED_STIPULATIONS)
    # The only "N" cell is MirrorBot self-play, read from the kernel.
    n_cells = [
        (r, c)
        for r in m.bots
        for c in m.bots
        if m.cell(r, c).row_action == "N" or m.cell(r, c).col_action == "N"
    ]
    assert n_cells == [("MirrorBot", "MirrorBot")]
    assert not m.cell("MirrorBot", "MirrorBot").hypothetical


def test_every_named_zoo_loads() -> None:
    """The registry is the UI dropdown's source of truth — all of it must work.

    A zoo whose stipulations have gone stale (a cell got proven) raises here,
    which is the intended way to notice.
    """
    for key, zoo in ZOOS.items():
        m = zoo.load()
        assert m.bots == zoo.bots, key
        assert (len(m.hypothetical_cells) == 0) == (len(zoo.stipulations) == 0), key


def test_named_zoo_provenance_claims_hold() -> None:
    """The zoos advertised as kernel-clean really carry no stipulations."""
    assert ZOOS["full-certified"].load().is_fully_proven
    assert ZOOS["proven-only"].load().is_fully_proven
    assert not ZOOS["enlarged"].load().is_fully_proven
    assert DEFAULT_ZOO in ZOOS


def test_unknown_zoo_lists_the_valid_keys() -> None:
    with pytest.raises(KeyError, match="unknown zoo"):
        get_zoo("no-such-zoo")


def test_enlarged_zoo_twin_structure() -> None:
    """The documented twin census for the 16-bot zoo (conditional on stipulations)."""
    m = load_tau_matrix(ENLARGED_SUB_ZOO, hypothetical_cells=ENLARGED_STIPULATIONS)
    assert sorted(behavioral_twins(m)) == [
        ("CooperateBot", "LegibleBot"),
        ("DupocBot", "JustBot"),
    ]


# ------------------------------------------------- hypothetical (what-if) ----

def test_hypothetical_cells_fill_holes_and_are_flagged() -> None:
    """What-if cells complete a submatrix but never masquerade as proven."""
    m = load_tau_matrix(
        hypothetical_cells=dict.fromkeys(CUPOD_STIPULATIONS, ("C", "D"))
    )
    assert not m.is_fully_proven
    assert m.cell("CupodBot", "DupocBot").shape == "HYPOTHETICAL"
    # The transpose is derived, so the two orientations cannot disagree.
    assert m.action("CupodBot", "DupocBot") == "C"
    assert m.action("DupocBot", "CupodBot") == "D"
    # Proven cells in the same matrix stay proven.
    assert not m.cell("CooperateBot", "DefectBot").hypothetical


def test_hypothetical_cannot_override_a_proven_cell() -> None:
    """Stipulating a proven pair would silently contradict the Lean kernel."""
    with pytest.raises(ValueError, match="only fill unproven holes"):
        load_tau_matrix(
            hypothetical_cells={("CooperateBot", "DefectBot"): ("D", "D")}
        )


def test_full_zoo_has_no_hypothetical_cells() -> None:
    """The 12-bot maximal zoo is kernel-backed end to end."""
    assert load_tau_matrix(bots=FULL_CERTIFIED_SUB_ZOO).is_fully_proven


def test_cupodtrollbot_split_is_earned_not_stipulated() -> None:
    """CupodBot's column separates CupodTrollBot on PROVEN data alone.

    `outcome_CupodTrollBot_vs_CupodBot` already exists, so this split holds
    under EVERY assignment of the unproven CupodBot cells — it was hidden only
    because CupodBot sits outside the certified sub-zoo for unrelated reasons.
    Contrast `DupocBot`/`JustBot` in the full zoo, which split only when a
    stipulation happens to disagree: a what-if result is trustworthy exactly
    when it is invariant across the stipulations.
    """
    import itertools

    holes = tuple(CUPOD_STIPULATIONS)
    values = [("C", "C"), ("C", "D"), ("D", "C"), ("D", "D")]
    for combo in itertools.product(values, repeat=len(holes)):
        m = load_tau_matrix(hypothetical_cells=dict(zip(holes, combo)))
        assert all("CupodTrollBot" not in g for g in behavioral_twins(m))


def test_justbot_split_depends_on_the_stipulation() -> None:
    """The DupocBot/JustBot split is an ARTIFACT of disagreeing stipulations.

    Over the full zoo (JustBot included), admitting CupodBot separates the pair
    only when the two stipulated cells assign them different actions against
    CupodBot. Half of the assignments split them, half do not — so no result
    should rest on it.
    """
    import itertools

    bots = tuple(sorted(FULL_CERTIFIED_SUB_ZOO + ("CupodBot",)))
    holes = (("CupodBot", "DupocBot"), ("CupodBot", "JustBot"), ("CupodBot", "PrudentBot"))
    values = [("C", "C"), ("C", "D"), ("D", "C"), ("D", "D")]

    split = 0
    for combo in itertools.product(values, repeat=3):
        m = load_tau_matrix(bots=bots, hypothetical_cells=dict(zip(holes, combo)))
        groups = behavioral_twins(m)
        if all({"DupocBot", "JustBot"} - set(g) for g in groups):
            split += 1
        # CooperateBot/LegibleBot survive every assignment — irreducibly twinned.
        assert any({"CooperateBot", "LegibleBot"} <= set(g) for g in groups)

    assert split == 32  # exactly half: a coin flip on an arbitrary choice


# ---------------------------------------------------------------- signal ----

def test_point_mass_and_uniform_are_distributions() -> None:
    assert Signal.point_mass("DefectBot").weights == {"DefectBot": 1.0}
    u = Signal.uniform(CERTIFIED_SUB_ZOO)
    assert math.isclose(sum(u.weights.values()), 1.0)
    assert math.isclose(u.entropy(), math.log2(len(CERTIFIED_SUB_ZOO)))


def test_signal_rejects_non_normalized() -> None:
    with pytest.raises(ValueError, match="sum to 1"):
        Signal({"DefectBot": 0.5})


def test_distance_is_a_pseudometric(matrix) -> None:
    d = behavioral_distance_matrix(matrix)
    for a in matrix.bots:
        assert d[(a, a)] == 0
        for b in matrix.bots:
            assert d[(a, b)] == d[(b, a)]
            for c in matrix.bots:  # triangle inequality
                assert d[(a, c)] <= d[(a, b)] + d[(b, c)]


def test_softmax_limits(matrix) -> None:
    """t → 0 is a point mass; t → ∞ is uniform."""
    cold = softmax_signal("DefectBot", matrix, temperature=0.0)
    assert cold.weights == {"DefectBot": 1.0}

    hot = softmax_signal("DefectBot", matrix, temperature=1e6)
    for p in hot.weights.values():
        assert math.isclose(p, 1.0 / len(matrix), rel_tol=1e-3)


def test_softmax_is_peaked_at_the_truth(matrix) -> None:
    for bot in matrix.bots:
        s = softmax_signal(bot, matrix, temperature=1.0)
        assert s.weights[bot] == max(s.weights.values())


def test_transparency_is_monotone_decreasing(matrix) -> None:
    d = behavioral_distance_matrix(matrix)
    ts = [0.05, 0.2, 0.5, 1.0, 2.0, 5.0, 20.0, 100.0]
    values = [transparency(matrix, t, d) for t in ts]
    assert all(a >= b - 1e-9 for a, b in zip(values, values[1:]))
    assert values[-1] < 0.01  # opaque limit


def test_transparency_is_continuous_at_zero(matrix) -> None:
    """No jump at t=0: the scale must measure the softmax channel throughout.

    The exact point mass identifies the bot BY NAME, which would read 1.0 and
    silently compare a different object against the behavioral channel.
    """
    d = behavioral_distance_matrix(matrix)
    assert math.isclose(
        transparency(matrix, 0.0, d), transparency(matrix, 1e-7, d), abs_tol=1e-6
    )


def test_behavioral_twins_share_a_row(matrix) -> None:
    """A twin group is exactly a set of bots with an identical action row."""
    for group in behavioral_twins(matrix):
        for other in group[1:]:
            assert matrix.row(group[0]) == matrix.row(other)


def test_default_zoo_is_twin_free(matrix) -> None:
    """No twins ⇒ transparency reaches exactly 1.0: behavior identifies the bot.

    This is what admitting CupodBot buys. Without it the residual
    {CooperateBot, CupodTrollBot} pair caps the scale at ≈0.940.
    """
    assert behavioral_twins(matrix) == []
    assert transparency(matrix, 0.0) == pytest.approx(1.0)


def test_twins_cap_transparency_below_one() -> None:
    """Twins are unresolvable by ANY behavioral signal, so the ceiling is < 1.

    The residual is exactly the syntactic information only a term-reading
    (Löbian) agent can exploit — the behavioral/prover split, visible in v1a.
    """
    for bots in (FULL_CERTIFIED_SUB_ZOO, PROVEN_ONLY_SUB_ZOO):
        m = load_tau_matrix(bots=bots)
        assert behavioral_twins(m)
        assert transparency(m, 0.0) < 1.0


def test_admitting_cupodbot_raises_the_ceiling() -> None:
    """Each step must buy transparency, or it costs bots for nothing."""
    full = transparency(load_tau_matrix(bots=FULL_CERTIFIED_SUB_ZOO), 0.0)
    proven_only = transparency(load_tau_matrix(bots=PROVEN_ONLY_SUB_ZOO), 0.0)
    default = transparency(load_tau_matrix(), 0.0)
    assert full < proven_only < default == pytest.approx(1.0)


def test_twin_freeness_is_invariant_under_the_stipulations() -> None:
    """The what-if buys MEMBERSHIP, not the result.

    All 16 assignments of CupodBot's two unproven cells give a twin-free zoo at
    ceiling 1.0, so twin-freeness does not depend on the values chosen. A
    what-if result is trustworthy exactly when it is invariant like this.
    """
    import itertools

    holes = tuple(CUPOD_STIPULATIONS)
    values = [("C", "C"), ("C", "D"), ("D", "C"), ("D", "D")]
    for combo in itertools.product(values, repeat=len(holes)):
        m = load_tau_matrix(hypothetical_cells=dict(zip(holes, combo)))
        assert behavioral_twins(m) == []
        assert transparency(m, 0.0) == pytest.approx(1.0)


def test_temperature_for_transparency_inverts(matrix) -> None:
    ceiling = transparency(matrix, 0.0)
    for target in (0.1, 0.3, 0.5):
        t = temperature_for_transparency(matrix, target)
        assert math.isclose(transparency(matrix, t), target, abs_tol=0.02)
    # At or above the ceiling, full transparency (t = 0) is the answer.
    assert temperature_for_transparency(matrix, ceiling) == 0.0


# ------------------------------------------------------------------ play ----

def test_coop_mass_under_point_mass_is_binary(matrix) -> None:
    for actor in matrix.bots:
        for hyp in matrix.bots:
            mass = coop_mass(matrix, actor, Signal.point_mass(hyp))
            assert mass == (1.0 if matrix.cooperates(actor, hyp) else 0.0)


def test_anchor_theorem_pointwise(matrix) -> None:
    """TauA(δ_B) plays exactly what A plays against B, for every α ∈ (0, 1]."""
    for actor in matrix.bots:
        for hyp in matrix.bots:
            signal = Signal.point_mass(hyp)
            for alpha in (1e-9, 0.25, 0.5, 0.75, 1.0):
                assert tau_play(matrix, actor, alpha, signal) == matrix.action(actor, hyp)


def test_anchor_theorem_tournament(matrix) -> None:
    """The whole t = 1 (full transparency) tournament IS the base matrix."""
    for alpha in (0.25, 0.5, 0.75, 1.0):
        assert anchor_holds(matrix, alpha)
    assert run_tournament(matrix, 1.0, 0.5).cells == base_tournament_cells(matrix)


def test_alpha_zero_is_unconditional_cooperation(matrix) -> None:
    """`≥ α` tie-breaking: α = 0 means cooperate no matter what."""
    signal = Signal.point_mass("DefectBot")
    for actor in matrix.bots:
        assert tau_play(matrix, actor, 0.0, signal) == "C"


def test_alpha_above_one_is_unconditional_defection(matrix) -> None:
    signal = Signal.uniform(matrix.bots)
    for actor in matrix.bots:
        assert tau_play(matrix, actor, 1.001, signal) == "D"


def test_unanimous_mass_cooperates_at_alpha_one(matrix) -> None:
    """α = 1 boundary must survive float summation error.

    CooperateBot cooperates against every hypothesis, so its mass is exactly
    1 — but naively summing the softmax weights lands an ULP short and would
    flip it to D on precisely the boundary the phase diagrams sit on.
    """
    channel = signal_family(matrix, t=0.2)
    for signal in channel.values():
        assert coop_mass(matrix, "CooperateBot", signal) == pytest.approx(1.0)
        assert tau_play(matrix, "CooperateBot", 1.0, signal) == "C"


def test_tau_play_is_monotone_in_alpha(matrix) -> None:
    """Raising caution can only ever turn C into D, never the reverse."""
    channel = signal_family(matrix, t=0.5)
    for actor in matrix.bots:
        for signal in channel.values():
            flips = [
                tau_play(matrix, actor, a, signal)
                for a in (0.1, 0.3, 0.5, 0.7, 0.9, 1.0)
            ]
            assert "C" not in flips[flips.index("D"):] if "D" in flips else True


def test_constant_bots_are_alpha_insensitive(matrix) -> None:
    """CooperateBot/DefectBot play the same regardless of blur or caution."""
    channel = signal_family(matrix, t=0.2)
    for signal in channel.values():
        assert tau_play(matrix, "CooperateBot", 1.0, signal) == "C"
        assert tau_play(matrix, "DefectBot", 1e-9, signal) == "D"


def test_uniform_signal_gives_unconditional_strategies(matrix) -> None:
    """Zero transparency ⇒ cooperation mass is constant per agent ⇒ classical PD."""
    uniform = Signal.uniform(matrix.bots)
    channel = {b: uniform for b in matrix.bots}
    for actor in matrix.bots:
        actions = {
            tau_match(matrix, actor, opp, 0.5, channel).row_action
            for opp in matrix.bots
        }
        assert len(actions) == 1


def test_alpha_breakpoints_capture_every_transition(matrix) -> None:
    """Between consecutive breakpoints behavior is constant, so a sweep is exact."""
    channel = signal_family(matrix, t=0.5)
    breaks = alpha_breakpoints(matrix, channel, quantize=9)
    assert breaks[0] == 0.0

    for lo, hi in zip(breaks, breaks[1:]):
        if hi - lo < 1e-6:
            continue
        mid_a, mid_b = lo + (hi - lo) * 0.3, lo + (hi - lo) * 0.7
        for actor in matrix.bots:
            for signal in channel.values():
                assert tau_play(matrix, actor, mid_a, signal) == tau_play(
                    matrix, actor, mid_b, signal
                )


def test_exact_breakpoints_are_rational(matrix) -> None:
    """The v1b Lean core works over ℚ; breakpoints must be exact there."""
    signal = Signal.uniform(matrix.bots)
    breaks = exact_alpha_breakpoints(matrix, signal)
    n = len(matrix.bots)
    for b in breaks:
        assert (b * n).denominator == 1  # k/n for some integer k


# ----------------------------------------------------------------- sweep ----

def test_report_renders_valid_svg(matrix) -> None:
    """The report is hand-rolled SVG, so malformed output is a real risk."""
    import re
    import xml.etree.ElementTree as ET

    from pd_runner.tau.report import build_report

    from pd_runner.tau.channels import all_families
    from pd_runner.tau.report import _SLIDER_ALPHAS, _SLIDER_TRANSPARENCIES

    page = build_report(matrix, alphas=(0.3, 0.62))
    svgs = re.findall(r"<svg.*?</svg>", page, re.S)
    # Per family: line + phase (2); composition + thresholds per slider α;
    # per-bot α-deviation per slider t; per-bot composition per (α, t) — the
    # only view needing BOTH cursors. Plus the family-comparison chart per α.
    n_fams = len(all_families(matrix))
    n_alphas, n_ts = len(_SLIDER_ALPHAS), len(_SLIDER_TRANSPARENCIES)
    assert len(svgs) == (
        n_fams * (2 + 2 * n_alphas + n_ts + n_alphas * n_ts) + n_alphas
    )
    for svg in svgs:
        ET.fromstring(svg)  # raises on malformed markup

    # No non-finite value may reach a coordinate.
    assert not re.search(r'[="\s,\-](nan|inf(inity)?)["\s,;)]', page, re.I)
    # Stipulated cells must be visually marked, not silently blended in.
    assert ("hyp" in page) == bool(matrix.hypothetical_cells)


def test_composition_partitions_every_cell(matrix) -> None:
    """The three outcome classes are exhaustive and disjoint: they sum to 1."""
    for t in (1.0, 0.5, 0.2, 0.0):
        composition = run_tournament(matrix, t, 0.45).composition
        assert set(composition) == {"CC", "exploit", "DD"}
        assert sum(composition.values()) == pytest.approx(1.0)
        assert all(v >= 0.0 for v in composition.values())


def test_composition_cc_matches_the_headline_rate(matrix) -> None:
    """The CC band must be the same number chart 1 plots, not a recomputation."""
    for t in (1.0, 0.3, 0.0):
        result = run_tournament(matrix, t, 0.45)
        assert result.composition["CC"] == pytest.approx(result.mutual_coop_rate)


def test_per_bot_composition_partitions_each_row(matrix) -> None:
    """Chart 3b's bars must account for every opponent, exactly once.

    Also pins the asymmetry that motivates the chart: (D,C) and (C,D) are
    tracked separately, so a bot's exploiting and being exploited never merge
    into chart 3's pooled "exploitation" band.
    """
    from pd_runner.tau.report import per_bot_composition

    for t in (1.0, 0.5, 0.0):
        counts = per_bot_composition(matrix, 0.45, t)
        assert set(counts) == set(matrix.bots)
        for bot, c in counts.items():
            assert sum(c.values()) == len(matrix.bots), bot
            assert all(v >= 0 for v in c.values())

    # At full transparency the row IS the base matrix row, so the per-bot
    # counts must reproduce it exactly — the anchor theorem, per bot.
    counts = per_bot_composition(matrix, 0.45, 1.0)
    for bot in matrix.bots:
        expected = {"CC": 0, "DC": 0, "CD": 0, "DD": 0, "other": 0}
        for opp in matrix.bots:
            cell = matrix.cell(bot, opp)
            key = f"{cell.row_action}{cell.col_action}"
            expected[key if key in expected else "other"] += 1
        assert counts[bot] == expected, bot


def test_per_bot_composition_totals_match_the_aggregate(matrix) -> None:
    """Chart 3b must be a decomposition of chart 3, not a second computation."""
    from pd_runner.tau.report import per_bot_composition

    for t in (0.8, 0.4):
        counts = per_bot_composition(matrix, 0.45, t)
        aggregate = run_tournament(matrix, t, 0.45).composition
        total = len(matrix.bots) ** 2
        cc = sum(c["CC"] for c in counts.values())
        dd = sum(c["DD"] for c in counts.values())
        exploit = sum(c["DC"] + c["CD"] for c in counts.values())
        assert cc / total == pytest.approx(aggregate["CC"])
        assert dd / total == pytest.approx(aggregate["DD"])
        assert exploit / total == pytest.approx(aggregate["exploit"])


def test_deviation_is_zero_at_full_transparency(matrix) -> None:
    """The anchor theorem, as the deviation charts must render it.

    At t = 1 every tau row equals its base row, so charts 4/4b must be
    uniformly "unchanged". If this breaks, the colour gradient is showing
    drift that the lift does not actually have.
    """
    from pd_runner.tau.report import alpha_deviation, row_deviation

    profile = row_deviation(matrix, 0.45, [1.0])
    assert {d for pts in profile.values() for _, d in pts} == {0.0}

    per_alpha = alpha_deviation(matrix, 1.0)
    assert {d for pts in per_alpha.values() for _, d in pts} == {0.0}


def test_deviation_agrees_with_the_thresholds(matrix) -> None:
    """Chart 4's threshold TICK and its COLOUR must come from the same event.

    The strip spans the whole axis and the tick marks where it stops being
    grey, so the first transparency at which deviation goes non-zero has to be
    exactly the reported threshold — otherwise the tick floats free of the
    shading it is supposed to explain.
    """
    from pd_runner.tau.report import robustness_thresholds, row_deviation

    grid = [round(1.0 - 0.05 * i, 3) for i in range(21)]
    thresholds = robustness_thresholds(matrix, 0.45, grid)
    deviation = row_deviation(matrix, 0.45, grid)
    for bot in matrix.bots:
        by_t = dict(deviation[bot])
        first_nonzero = next((t for t in grid if by_t[t] > 0.0), None)
        assert first_nonzero == thresholds[bot], bot


def test_threshold_strip_colours_the_drifted_side(matrix) -> None:
    """The regression that motivated the strip: colour the RIGHT side of the tick.

    Deviation grows as transparency FALLS, so the informative region is the
    blurrier side. An earlier version shaded the span from full transparency
    down to the threshold — i.e. exactly the region that is unchanged by
    construction — leaving every bar uniformly grey and the gradient useless.
    Here: left of the tick must be entirely unchanged, and a bot that does
    deviate must show real colour to the right of it.
    """
    import re

    from pd_runner.tau.report import (
        _deviation_colour,
        _threshold_chart,
        robustness_thresholds,
        row_deviation,
    )

    grid = [round(1.0 - 0.05 * i, 3) for i in range(21)]
    thresholds = robustness_thresholds(matrix, 0.45, grid)
    deviation = row_deviation(matrix, 0.45, grid)
    grey = _deviation_colour(0.0)

    # Semantic form: nothing has moved above the threshold, something has below.
    for bot, threshold in thresholds.items():
        if threshold is None:
            assert all(d == 0.0 for _, d in deviation[bot]), bot
            continue
        for t, d in deviation[bot]:
            if t > threshold + 1e-9:
                assert d == 0.0, (bot, t)
        assert max(d for t, d in deviation[bot] if t <= threshold + 1e-9) > 0.0, bot

    # Rendered form: for each deviating bot, the coloured part of its strip must
    # sit on the BLURRY side of the tick. Checking the boundary position — not
    # merely "some colour exists" — is what distinguishes the fix from the bug:
    # the inverted version also emitted a few coloured segments, but on the
    # wrong side and hugging the far edge.
    svg = _threshold_chart(thresholds, deviation)
    row_rects = re.findall(
        r'<rect x="([\d.]+)" y="(\d+)" width="([\d.]+)"[^>]*fill="(#[0-9a-f]{6})"', svg
    )
    assert row_rects, "threshold strip emitted no segments"

    by_row: dict[str, list[tuple[float, float, str]]] = {}
    for x, y, w, fill in row_rects:
        by_row.setdefault(y, []).append((float(x), float(w), fill))

    deviating = [b for b, t in thresholds.items() if t is not None]
    checked = 0
    for segments in by_row.values():
        segments.sort()
        span = sum(w for _, w, _ in segments)
        if span < 200:  # legend swatches, not a bot row
            continue
        coloured = [x for x, _, f in segments if f != grey]
        if not coloured:
            continue
        left = min(x for x, _, _ in segments)
        # Every coloured segment starts at or right of the grey/colour boundary,
        # and that boundary is strictly inside the strip (not pinned to the end).
        boundary = min(coloured)
        assert boundary > left, "colour starts at full transparency"
        assert boundary < left + span, "colour never begins"
        # The drifted region must be a real span, not a single tail segment.
        assert sum(w for x, w, f in segments if f != grey) > span * 0.02
        checked += 1
    assert checked == len(deviating), (checked, len(deviating))


def test_threshold_chart_axis_matches_its_marks(matrix) -> None:
    """Chart 4's x-axis labels must be placed through the strip's own map.

    The strip, the threshold tick and the axis all encode transparency as
    `pad_l + (1 - t) * plot_w` — full transparency LEFT, opaque right, like
    every other chart. The axis once ran the other way (`pad_l + t * plot_w`),
    which mirrored the labels against the marks: a bot whose threshold was 40%
    had its tick and its "40%" drawn at the pixel the axis called 60%.
    """
    import xml.etree.ElementTree as ET

    from pd_runner.tau.report import (
        _threshold_chart,
        robustness_thresholds,
        row_deviation,
    )

    width, pad_l, pad_r = 720, 130, 60
    plot_w = width - pad_l - pad_r

    def decode(x: float) -> float:
        """Pixel -> transparency, through the map the strip is drawn with."""
        return 1.0 - (x - pad_l) / plot_w

    grid = [round(1.0 - 0.05 * i, 3) for i in range(21)]
    thresholds = robustness_thresholds(matrix, 0.45, grid)
    root = ET.fromstring(
        _threshold_chart(thresholds, row_deviation(matrix, 0.45, grid))
    )

    axis = [
        e for e in root.iter()
        if e.tag.endswith("text") and e.get("class") == "tick mid"
        and (e.text or "").endswith("%")
    ]
    assert len(axis) == 5
    for label in axis:
        printed = float(label.text.rstrip("%")) / 100
        assert decode(float(label.get("x"))) == pytest.approx(printed, abs=5e-3)

    # Each row's printed threshold must sit exactly on its tick.
    ticks = sorted(
        (e for e in root.iter()
         if e.tag.endswith("line") and e.get("stroke") == "#1a1a1a"),
        key=lambda e: float(e.get("y1")),
    )
    row_labels = sorted(
        (e for e in root.iter()
         if e.tag.endswith("text") and e.get("class") == "tick end"
         and (e.text or "").endswith("%")),
        key=lambda e: float(e.get("y")),
    )
    deviating = [t for t in thresholds.values() if t is not None]
    assert len(ticks) == len(row_labels) == len(deviating)
    for tick, label in zip(ticks, row_labels):
        printed = float(label.text.rstrip("%")) / 100
        assert decode(float(tick.get("x1"))) == pytest.approx(printed, abs=5e-3)


def test_deviation_is_not_monotone_in_transparency(matrix) -> None:
    """Deviation can DECREASE as the signal degrades — pinned as a real fact.

    A bot may depart from its base row and later return to it. As t → 0 every
    signal converges to the same uniform mixture, so every opponent's
    cooperation mass converges to one limit (the actor's own base cooperation
    fraction); masses reaching it from opposite sides can cross α in opposite
    directions at nearby t, dipping the flipped-cell count.

    This is asserted rather than merely tolerated because the obvious "tidying"
    — clamping the profile to a running maximum, or trusting the threshold as
    a permanent departure — would look like a cleanup and would be a lie. If
    this test ever fails, the sweep changed; do not delete it to make the chart
    look monotone.
    """
    from pd_runner.tau.report import row_deviation

    grid = [round(1.0 - 0.025 * i, 3) for i in range(41)]
    dips = [
        (alpha, bot, points[i][0], points[i][1], points[i + 1][1])
        for alpha in (0.25, 0.7)
        for bot, points in row_deviation(matrix, alpha, grid).items()
        for i in range(len(points) - 1)
        if points[i + 1][1] < points[i][1] - 1e-12
    ]
    assert dips, "expected at least one non-monotone deviation profile"
    # The dips live at the opaque end, where the masses bunch near their limit.
    assert all(t <= 0.5 for _, _, t, _, _ in dips)


def test_returning_rows_are_marked_in_the_chart(matrix) -> None:
    """A non-permanent departure must be flagged, not silently ticked.

    The threshold is the FIRST departure. Where a bot returns to its base row
    at lower transparency, the tick alone reads as "needs this much
    transparency", which is false — so those rows carry a `°`.
    """
    import re

    from pd_runner.tau.report import (
        _threshold_chart,
        robustness_thresholds,
        row_deviation,
    )

    grid = [round(1.0 - 0.05 * i, 3) for i in range(21)]
    alpha = 0.25  # OBot returns to base at t = 0.05 under this α.
    thresholds = robustness_thresholds(matrix, alpha, grid)
    deviation = row_deviation(matrix, alpha, grid)

    returning = {
        bot
        for bot, threshold in thresholds.items()
        if threshold is not None
        and any(d == 0.0 for t, d in deviation[bot] if t <= threshold + 1e-9)
    }
    assert returning, "fixture no longer exercises a returning row"

    svg = _threshold_chart(thresholds, deviation)
    marked = len(re.findall(r"°", svg))
    assert marked == len(returning), (marked, sorted(returning))
    # And the degree mark never appears when nothing returns.
    flat = {b: 1.0 for b in matrix.bots}
    assert "°" not in _threshold_chart(
        flat, {b: [(1.0, 0.5), (0.5, 0.5)] for b in matrix.bots}
    )


def test_unconditional_bots_never_deviate(matrix) -> None:
    """Constant bots have no conditionality to lose, on either dial."""
    from pd_runner.tau.report import alpha_deviation, row_deviation

    grid = [round(1.0 - 0.1 * i, 2) for i in range(11)]
    by_t = row_deviation(matrix, 0.45, grid)
    by_alpha = alpha_deviation(matrix, 0.5)
    for bot in ("CooperateBot", "DefectBot"):
        assert max(d for _, d in by_t[bot]) == 0.0, bot
        assert max(d for _, d in by_alpha[bot]) == 0.0, bot


def test_deviation_colour_ramp_is_monotone_and_valid(matrix) -> None:
    """Every deviation maps to a well-formed hex colour, darkening with drift."""
    import re

    from pd_runner.tau.report import _deviation_colour

    previous = None
    for i in range(21):
        colour = _deviation_colour(i / 20)
        assert re.fullmatch(r"#[0-9a-f]{6}", colour), colour
        luminance = sum(int(colour[j:j + 2], 16) for j in (1, 3, 5))
        if previous is not None:
            assert luminance <= previous, f"ramp brightens at {i / 20}"
        previous = luminance
    # Out-of-range input clamps rather than producing a broken colour.
    assert _deviation_colour(-1.0) == _deviation_colour(0.0)
    assert _deviation_colour(2.0) == _deviation_colour(1.0)


def test_blur_converts_defection_into_cooperation(matrix) -> None:
    """The reason the CC band alone is misleading, pinned as a fact.

    Going from full transparency to none, mutual cooperation RISES while mutual
    defection falls — cooperation is displacing (D,D), not being earned. A
    rising blue band at low transparency is bots losing the ability to
    condition, not cooperation improving.
    """
    clear = run_tournament(matrix, 1.0, 0.45).composition
    opaque = run_tournament(matrix, 0.0, 0.45).composition
    assert opaque["CC"] > clear["CC"]
    assert opaque["DD"] < clear["DD"]


def test_report_alpha_slider(matrix) -> None:
    """Charts 2/3 are α-sensitive; the slider must expose every grid value.

    The report is static HTML, so interactivity means one pre-rendered panel
    pair per grid α, exactly one pair visible, and readouts naming the initial
    α — which starts at the true middle of the requested alphas (lower-middle
    for an even-length tuple; the upper-middle once silently showed a
    different α than the reader expected).
    """
    import re

    from pd_runner.tau.report import _SLIDER_ALPHAS, build_report

    alpha_view = re.compile(
        r'class="panel swap-view" data-alpha="([^"]+)"'
        r'(?: data-family="\w+")?(?: data-transparency="[^"]+")?( hidden)?>'
    )

    page = build_report(matrix, alphas=(0.3, 0.45, 0.62, 0.8))
    views = alpha_view.findall(page)
    # Every slider value appears (comparison + composition + per-bot mix +
    # thresholds views)…
    assert {a for a, _ in views} == {f"{a:g}" for a in _SLIDER_ALPHAS}
    # …and exactly the initial α's views are visible (one per α-driven chart:
    # 2, 3, 3b, 4 — 3b is additionally gated on t, which starts mid-dial).
    assert [a for a, h in views if not h] == ["0.45"] * 4
    assert '<span class="pill alpha-readout">α = 0.45</span>' in page
    # Five synced copies: the top control plus one under each α-driven chart
    # (2, 3, 3b, 4), so α can be adjusted where it is being read. All must
    # start at the same grid index or the page opens out of sync.
    starts = re.findall(r'class="alpha-slider"[^>]*value="(\d+)"', page)
    assert len(starts) == 5
    assert len(set(starts)) == 1

    # Odd-length tuples start at the exact middle (snapped to the grid);
    # a single family keeps this second build fast.
    page = build_report(matrix, alphas=(0.2, 0.5, 0.9), families=("behavioral",))
    assert [a for a, h in alpha_view.findall(page) if not h] == ["0.5"] * 4


def test_report_names_the_zoo(matrix) -> None:
    """Results are zoo-dependent, so the membership must be on the page."""
    from pd_runner.tau.report import build_report

    page = build_report(matrix, alphas=(0.45,))
    for bot in matrix.bots:
        assert bot in page


def test_report_sweep_hits_its_transparency_targets(matrix) -> None:
    """The x-axis is only meaningful if the bisection actually inverts."""
    from pd_runner.tau.report import sweep_by_transparency

    for point in sweep_by_transparency(matrix, 0.45, [1.0, 0.75, 0.5, 0.25]):
        assert point.actual_transparency == pytest.approx(
            point.target_transparency, abs=0.02
        )


def test_robustness_thresholds_spare_the_constant_bots(matrix) -> None:
    """Constant bots have no conditionality to lose, so blur cannot move them."""
    from pd_runner.tau.report import robustness_thresholds

    thresholds = robustness_thresholds(
        matrix, 0.45, [round(1.0 - 0.05 * i, 3) for i in range(21)]
    )
    assert thresholds["CooperateBot"] is None
    assert thresholds["DefectBot"] is None
    # …while at least one conditional bot does deviate.
    assert any(v is not None for v in thresholds.values())


def test_tau_report_endpoint() -> None:
    """`GET /tau/report` serves the report fresh; bad alphas fail loudly."""
    pytest.importorskip("fastapi")
    from fastapi.testclient import TestClient

    from pd_runner.api.main import app

    client = TestClient(app)
    from pd_runner.tau.report import _SLIDER_ALPHAS, _SLIDER_TRANSPARENCIES

    n_a, n_t = len(_SLIDER_ALPHAS), len(_SLIDER_TRANSPARENCIES)
    page = client.get("/tau/report?alphas=0.5")
    assert page.status_code == 200
    assert page.headers["content-type"].startswith("text/html")
    assert "TauBots" in page.text
    assert page.text.count("<svg") == 3 * (2 + 2 * n_a + n_t + n_a * n_t) + n_a
    # top + charts 2, 3, 3b, 4
    assert page.text.count('class="alpha-slider"') == 5
    assert page.text.count('class="t-slider"') == 2  # charts 3b, 4b
    assert 'name="family"' in page.text  # σ-family selector

    assert client.get("/tau/report?alphas=abc").status_code == 400
    assert client.get("/tau/report?alphas=,").status_code == 400

    # The UI carries the trigger.
    index = client.get("/")
    assert "openTauReport" in index.text and "Run tau analysis" in index.text


# --------------------------------------------------- σ channel families ----

def test_every_zoo_bot_parses_to_an_ast(matrix) -> None:
    """Every zoo bot's Lean definition must parse into a `Prog` tree.

    The reader is strict by design: a source shape it does not recognize
    raises rather than yielding a partial tree, because a silently truncated
    AST would poison every distance involving that bot.
    """
    from pd_runner.tau.syntax import bot_asts

    asts = bot_asts(matrix.bots)
    assert set(asts) == set(matrix.bots)
    # Anchors: the constants are `const(action)` pairs; DupocBot is a searcher.
    assert asts["CooperateBot"].label == "const"
    assert asts["CooperateBot"].size == 2
    assert asts["DupocBot"].label == "search"
    assert asts["DBot"].label == "ite"


def test_tree_edit_distance_matches_hand_computed_cases() -> None:
    """Unit-cost Zhang–Shasha, checked against cases with known answers."""
    from pd_runner.tau.syntax import Node, tree_edit_distance as ted

    assert ted(Node("a"), Node("a")) == 0
    assert ted(Node("a"), Node("b")) == 1
    # Deleting a child, inserting one, and swapping two.
    f_ab = Node("f", (Node("a"), Node("b")))
    assert ted(f_ab, Node("f", (Node("a"),))) == 1
    assert ted(f_ab, Node("f", (Node("a"), Node("b"), Node("c")))) == 1
    assert ted(f_ab, Node("f", (Node("b"), Node("a")))) == 2
    # The classic Zhang–Shasha worked example (answer: 2).
    x = Node("f", (Node("d", (Node("a"), Node("c", (Node("b"),)))), Node("e")))
    y = Node("f", (Node("c", (Node("d", (Node("a"), Node("b"))),)), Node("e")))
    assert ted(x, y) == 2
    assert ted(x, y) == ted(y, x)


def test_ast_distance_separates_the_v1_feature_twins(matrix) -> None:
    """DBot vs TitForTatBot: the defect the AST channel exists to fix.

    Both are `.ite (.sim .opp (.bot X)) C · ·` — identical constructor BAGS,
    so the v1 feature vector called them twins. They differ in the probe
    target (DefectBot vs CooperateBot) and in which branch cooperates, and the
    AST sees both edits.
    """
    from pd_runner.tau.syntax import feature_distance_matrix, syntactic_distance_matrix

    assert feature_distance_matrix(matrix)[("DBot", "TitForTatBot")] == 0
    assert syntactic_distance_matrix(matrix)[("DBot", "TitForTatBot")] > 0


def test_ast_distance_is_scale_free(matrix) -> None:
    """Distance must not be dominated by program SIZE (the v1 defect).

    Unnormalized L1 correlated ≈ +0.75 with node count: big bots were far from
    everything, and the softmax read that as "big bots are identifiable".
    Normalizing by the larger tree removes it.
    """
    import statistics

    from pd_runner.tau.syntax import bot_ast, syntactic_distance_matrix

    dist = syntactic_distance_matrix(matrix)
    sizes = [bot_ast(b).size for b in matrix.bots]
    means = [
        statistics.mean([dist[(b, c)] for c in matrix.bots]) for b in matrix.bots
    ]
    mx, my = statistics.mean(sizes), statistics.mean(means)
    cov = sum((x - mx) * (y - my) for x, y in zip(sizes, means))
    den = (
        sum((x - mx) ** 2 for x in sizes) * sum((y - my) ** 2 for y in means)
    ) ** 0.5
    assert abs(cov / den) < 0.45

    # And every distance is a bounded ratio, not an unbounded node count.
    assert all(0.0 <= d <= 10.0 for d in dist.values())


def test_confusion_structure_inversion(matrix) -> None:
    """The syntactic channel confuses what the behavioral one separates.

    Dupoc/Cupod: same tree, leaf action labels swapped — syntactic near-twins,
    behavioral opposites. The reverse holds for Coop/CupodTroll. This inversion
    is WHY the code channel is a separate object, and it must survive the v1→v2
    distance change.
    """
    from pd_runner.tau.signal import behavioral_distance_matrix
    from pd_runner.tau.syntax import syntactic_distance_matrix

    syn = syntactic_distance_matrix(matrix)
    beh = behavioral_distance_matrix(matrix)

    # Syntactically close, behaviorally far…
    assert syn[("DupocBot", "CupodBot")] < syn[("CooperateBot", "CupodTrollBot")]
    assert beh[("DupocBot", "CupodBot")] >= 5
    # …and the reverse: behavioral near-twins that are syntactic opposites.
    assert beh[("CooperateBot", "CupodTrollBot")] <= 1

    # Globally the two channels must stay near-uncorrelated, or the "second
    # object" claim collapses into a noisy copy of the behavioral one.
    pairs = [(a, b) for a in matrix.bots for b in matrix.bots if a < b]
    xs = [syn[p] for p in pairs]
    ys = [float(beh[p]) for p in pairs]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = (sum((x - mx) ** 2 for x in xs) * sum((y - my) ** 2 for y in ys)) ** 0.5
    assert abs(cov / den) < 0.4


def test_budget_arguments_are_erased(matrix) -> None:
    """Search budgets are a DIFFERENT transparency axis, not code identity.

    `CupodBot k` and `CupodBot (2 * k + 64)` are the same code to a source-
    reading observer; conflating budget with structure would silently merge
    Critch's depth dial into our breadth dial.
    """
    from pd_runner.tau.syntax import parse_prog

    plain = parse_prog(".search k (.eq .opp (CupodBot k)) (.const Action.D) (.const Action.C)")
    scaled = parse_prog(
        ".search (2 * k + 64) (.eq .opp (CupodBot (2 * k))) "
        "(.const Action.D) (.const Action.C)"
    )
    assert plain == scaled


def test_families_calibrate_to_the_same_dial(matrix) -> None:
    """At matched t below every ceiling, all families measure transparency ≈ t.

    This is the property that makes cross-family comparison meaningful: equal
    information RATE, differing only in confusion structure.
    """
    from pd_runner.tau.channels import all_families

    for family in all_families(matrix).values():
        for t in (0.8, 0.5, 0.2):
            assert family.transparency(t) == pytest.approx(t, abs=0.02), family.key


def test_family_ceilings(matrix) -> None:
    """A family's ceiling is 1.0 exactly when it has no twins to be blind to.

    All three reach 1.0 on this zoo: ε-uniform is identity-based, behavioral is
    twin-free here by construction, and the AST syntactic channel resolves the
    DBot/TitForTatBot pair that the v1 feature vector could not (that pair was
    the reason this used to assert `< 1.0`).
    """
    from pd_runner.tau.channels import all_families
    from pd_runner.tau.syntax import syntactic_twins

    fams = all_families(matrix)
    assert fams["epsilon"].ceiling() == pytest.approx(1.0)
    assert fams["behavioral"].ceiling() == pytest.approx(1.0)
    assert not syntactic_twins(matrix)
    assert fams["syntactic"].ceiling() == pytest.approx(1.0)


def test_epsilon_channel_shape(matrix) -> None:
    """The control is exactly (1-ε)·δ + ε·uniform at its raw knob."""
    from pd_runner.tau.channels import epsilon_family

    family = epsilon_family(matrix)
    channel = family._channel_at_raw(0.4)
    n = len(matrix.bots)
    for b in matrix.bots:
        assert channel[b].weights[b] == pytest.approx(0.6 + 0.4 / n)
        for other in matrix.bots:
            if other != b:
                assert channel[b].weights[other] == pytest.approx(0.4 / n)


def test_anchor_theorem_holds_for_every_family(matrix) -> None:
    """t = 1 reproduces the base matrix under EVERY channel family."""
    from pd_runner.tau.channels import all_families
    from pd_runner.tau.sweep import base_tournament_cells

    for family in all_families(matrix).values():
        # Now unconditional: with the AST channel every family reaches a true
        # point mass on this zoo, so no family gets an exemption.
        result = run_tournament(matrix, 1.0, 0.5, family=family)
        assert result.family == family.key
        assert result.cells == base_tournament_cells(matrix), family.key


def test_family_tournaments_differ_at_matched_transparency(matrix) -> None:
    """The point of the exercise: same information rate, different outcomes.

    If all families gave identical tournaments at matched t, the confusion
    structure would be irrelevant and one channel would suffice.
    """
    from pd_runner.tau.channels import all_families

    fams = all_families(matrix)
    cells = {
        key: run_tournament(matrix, 0.3, 0.45, family=fam).cells
        for key, fam in fams.items()
    }
    assert len({tuple(sorted(c.items())) for c in cells.values()}) > 1


def test_charts_carry_a_valid_cursor_payload(matrix) -> None:
    """Every x-axis chart ships hover data the cursor script can actually read.

    The payload is embedded as JSON in an attribute, so a quoting or escaping
    regression would silently disable the cursor on a rendered page rather
    than raising anywhere — hence parsing every payload back here.
    """
    import html as html_mod
    import json as json_mod
    import re

    from pd_runner.tau.report import build_report

    page = build_report(matrix, alphas=(0.45,))
    payloads = re.findall(r"data-cursor='([^']*)'", page)
    assert payloads, "no chart emitted cursor data"
    # One hit rectangle and one overlay layer per cursor-bearing chart.
    assert page.count('class="chart cursor-chart"') == len(payloads)
    assert page.count('class="cursor-hit"') == len(payloads)

    for blob in payloads:
        cfg = json_mod.loads(html_mod.unescape(blob))
        assert cfg["series"], "cursor payload has no series"
        assert cfg["plotW"] > 0 and cfg["plotH"] > 0
        lengths = {len(s["points"]) for s in cfg["series"]}
        # All series must share an x-grid; the script indexes them together.
        assert len(lengths) == 1
        for s in cfg["series"]:
            assert s["label"] and s["colour"]
            assert all(0.0 <= x <= 1.0 for x, _ in s["points"])


def test_composition_cursor_reads_bands_not_stacked_tops(matrix) -> None:
    """The stacked chart must report each band's own value.

    Reporting the cumulative tops would make the middle band read as
    "cooperation + exploitation", which is not a quantity anyone wants.
    """
    import html as html_mod
    import json as json_mod
    import re

    from pd_runner.tau.report import build_report

    page = build_report(matrix, alphas=(0.45,))
    for blob in re.findall(r"data-cursor='([^']*)'", page):
        cfg = json_mod.loads(html_mod.unescape(blob))
        if any("mutual cooperation" in s["label"] for s in cfg["series"]):
            for i in range(len(cfg["series"][0]["points"])):
                total = sum(s["points"][i][1] for s in cfg["series"])
                # Payload values are rounded to 6dp, so three bands can sum a
                # few ULP-scale units off exactly 1.
                assert total == pytest.approx(1.0, abs=5e-6)
            return
    pytest.fail("no composition chart found in the report")


def test_degenerate_label_stays_inside_the_plot(matrix) -> None:
    """The "degenerate" marker must not run into the legend column.

    The degenerate band is usually narrow — it can be zero-width when only the
    last sample is degenerate — so a left-anchored label drawn rightward
    overflowed the plot and printed on top of the "mutual cooperation" legend.
    Narrow bands right-anchor to the plot edge instead.
    """
    import re

    from pd_runner.tau.report import _DEGENERATE_LABEL_W, build_report

    # Geometry of `_composition_chart` at its defaults.
    plot_left, plot_right, legend_left = 56, 520, 536

    page = build_report(matrix, alphas=(0.3, 0.45))
    left = {
        float(x)
        for x in re.findall(
            r'<text x="([\d.]+)" y="[\d.]+" class="tick" fill="#d55e00">'
            r"degenerate</text>",
            page,
        )
    }
    right = {
        float(x)
        for x in re.findall(
            r'<text x="([\d.]+)" y="[\d.]+" class="tick end" fill="#d55e00">'
            r"degenerate</text>",
            page,
        )
    }
    assert left or right, "no degenerate marker rendered"
    # Left-anchored text grows rightward; right-anchored grows leftward.
    for x in left:
        assert x + _DEGENERATE_LABEL_W <= legend_left
    for x in right:
        assert x <= plot_right
        assert x - _DEGENERATE_LABEL_W >= plot_left


def test_report_shows_the_family_machinery(matrix) -> None:
    """The analysis page must expose all families: radio, table, comparison."""
    from pd_runner.tau.report import build_report

    page = build_report(matrix, alphas=(0.45,))
    assert page.count('type="radio" name="family"') == 3  # one per family
    assert "Channel comparison at matched transparency" in page
    assert "ε-uniform (null control)" in page
    assert "syntactic (AST)" in page
    # Every family's twin column renders — "—" when a family has none, which
    # is now the syntactic case (the AST resolves the old DBot/TFT pair).
    assert page.count("<td>") >= 3


def test_tournament_rates_are_consistent(matrix) -> None:
    r = run_tournament(matrix, t=0.5, alpha=0.5)
    assert 0.0 <= r.mutual_coop_rate <= r.coop_rate <= 1.0
    assert len(r.cells) == len(matrix) ** 2


def test_tournament_is_symmetric_under_transpose(matrix) -> None:
    """Cell (A,B) and cell (B,A) must describe the same match."""
    r = run_tournament(matrix, t=0.4, alpha=0.5)
    for (row, col), (a, b) in r.cells.items():
        assert r.cells[(col, row)] == (b, a)


def test_dial_matches_measured_transparency(matrix) -> None:
    """t IS the transparency: the dial and the measured MI must agree."""
    for t in (0.8, 0.5, 0.2):
        r = run_tournament(matrix, t, 0.45)
        assert r.t == t
        assert r.transparency == pytest.approx(t, abs=0.02)
    # The endpoints: t = 1 is the point mass, t = 0 is (near-)opaque.
    assert run_tournament(matrix, 1.0, 0.45).temperature == 0.0
    assert run_tournament(matrix, 0.0, 0.45).transparency < 0.01


def test_opaque_limit_is_degenerate(matrix) -> None:
    """The classical-PD limit at t = 0: everyone plays unconditionally.

    α is offset off the knife edge deliberately — see
    `test_knife_edge_alpha_is_noise_sensitive`.
    """
    r = run_tournament(matrix, t=0.0, alpha=0.42)
    assert r.is_degenerate
    assert r.transparency < 0.01


def test_knife_edge_alpha_is_noise_sensitive(matrix) -> None:
    """Documents a real fragility: α exactly on an achievable mass is unstable.

    At uniform σ an agent's cooperation mass is its coop FRACTION over the zoo.
    When α sits exactly on some agent's fraction, the ~1e-6 residual
    non-uniformity at finite temperature straddles the threshold and decides
    the play — the agent looks conditional at zero transparency when it is not.

    Sweeps must therefore step BETWEEN α breakpoints, never on them
    (`alpha_breakpoints` returns the achievable masses; use midpoints).
    """
    fractions = {
        b: sum(1 for o in matrix.bots if matrix.cooperates(b, o)) / len(matrix.bots)
        for b in matrix.bots
    }
    knife_edge = next(f for f in fractions.values() if 0.0 < f < 1.0)

    on_edge = run_tournament(matrix, t=0.0, alpha=knife_edge)
    assert not on_edge.is_degenerate  # spurious conditionality

    # Stepping off the edge (and clear of every other agent's fraction) is stable.
    for alpha in (knife_edge - 0.02, knife_edge + 0.02):
        assert run_tournament(matrix, t=0.0, alpha=alpha).is_degenerate

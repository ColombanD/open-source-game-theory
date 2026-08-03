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
    FULL_CERTIFIED_SUB_ZOO,
    PROVEN_ONLY_SUB_ZOO,
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


def test_mirrorbot_excluded_for_proven_none() -> None:
    """MirrorBot self-play is proven `none`; v1a does not model that value."""
    assert "MirrorBot" not in CERTIFIED_SUB_ZOO
    with pytest.raises(ValueError, match="not total"):
        load_tau_matrix(bots=("MirrorBot", "CooperateBot"))


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
    from pd_runner.tau.report import _SLIDER_ALPHAS

    page = build_report(matrix, alphas=(0.3, 0.62))
    svgs = re.findall(r"<svg.*?</svg>", page, re.S)
    # Per family: line + phase (2) and composition + thresholds per slider α;
    # plus the family-comparison chart per slider α.
    n_fams, n_alphas = len(all_families(matrix)), len(_SLIDER_ALPHAS)
    assert len(svgs) == n_fams * (2 + 2 * n_alphas) + n_alphas
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
        r'class="panel swap-view" data-alpha="([^"]+)"(?: data-family="\w+")?( hidden)?>'
    )

    page = build_report(matrix, alphas=(0.3, 0.45, 0.62, 0.8))
    views = alpha_view.findall(page)
    # Every slider value appears (comparison + composition + thresholds views)…
    assert {a for a, _ in views} == {f"{a:g}" for a in _SLIDER_ALPHAS}
    # …and exactly the initial α's views are visible (one per α-driven chart).
    assert [a for a, h in views if not h] == ["0.45"] * 3
    assert '<span class="pill alpha-readout">α = 0.45</span>' in page
    assert 'id="alpha-slider"' in page

    # Odd-length tuples start at the exact middle (snapped to the grid);
    # a single family keeps this second build fast.
    page = build_report(matrix, alphas=(0.2, 0.5, 0.9), families=("behavioral",))
    assert [a for a, h in alpha_view.findall(page) if not h] == ["0.5"] * 3


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
    from pd_runner.tau.report import _SLIDER_ALPHAS

    page = client.get("/tau/report?alphas=0.5")
    assert page.status_code == 200
    assert page.headers["content-type"].startswith("text/html")
    assert "TauBots" in page.text
    assert page.text.count("<svg") == 3 * (2 + 2 * len(_SLIDER_ALPHAS)) + len(_SLIDER_ALPHAS)
    assert 'id="alpha-slider"' in page.text
    assert 'name="family"' in page.text  # σ-family selector

    assert client.get("/tau/report?alphas=abc").status_code == 400
    assert client.get("/tau/report?alphas=,").status_code == 400

    # The UI carries the trigger.
    index = client.get("/")
    assert "openTauReport" in index.text and "Run tau analysis" in index.text


# --------------------------------------------------- σ channel families ----

def test_syntactic_features_cover_the_zoo(matrix) -> None:
    """Every zoo bot's Lean definition must parse to a feature vector.

    A silently missing definition would become a zero vector and poison every
    distance, so extraction fails loudly — this pins that it currently works
    for the whole default zoo.
    """
    from pd_runner.tau.syntax import FEATURE_ORDER, bot_feature_vectors

    vectors = bot_feature_vectors(matrix.bots)
    assert set(vectors) == set(matrix.bots)
    for vec in vectors.values():
        assert len(vec) == len(FEATURE_ORDER)
    # Sanity anchors: the constants are single leaves, DupocBot is a searcher.
    idx = {f: i for i, f in enumerate(FEATURE_ORDER)}
    assert vectors["CooperateBot"][idx["C"]] == 1
    assert sum(vectors["CooperateBot"]) == 1
    assert vectors["DupocBot"][idx["search"]] == 1


def test_confusion_structure_inversion(matrix) -> None:
    """The syntactic channel confuses what the behavioral one separates.

    Dupoc/Cupod: identical tree, leaf labels swapped — syntactic near-twins,
    behavioral opposites. Coop/Defect: adjacent constants, maximally distinct
    conduct. This inversion is WHY the code channel is a separate object.
    """
    from pd_runner.tau.signal import behavioral_distance_matrix
    from pd_runner.tau.syntax import syntactic_distance_matrix

    syn = syntactic_distance_matrix(matrix)
    beh = behavioral_distance_matrix(matrix)

    # Syntactically close, behaviorally far…
    assert syn[("DupocBot", "CupodBot")] <= 2
    assert beh[("DupocBot", "CupodBot")] >= 5
    assert syn[("CooperateBot", "DefectBot")] <= 2
    assert beh[("CooperateBot", "DefectBot")] == len(matrix)
    # …and the reverse: behavioral near-twins that are syntactic opposites.
    assert beh[("CooperateBot", "CupodTrollBot")] <= 1
    assert syn[("CooperateBot", "CupodTrollBot")] >= 4


def test_syntactic_twins_exist(matrix) -> None:
    """DBot/TitForTatBot: identical constructor profiles, opposite conduct.

    The syntactic channel's own blind spot (its ceiling < 1), mirroring the
    behavioral twins — an observer of structure who cannot resolve referenced
    bot NAMES cannot tell the zoo's exploiter from its reciprocator.
    """
    from pd_runner.tau.syntax import syntactic_twins

    assert ("DBot", "TitForTatBot") in syntactic_twins(matrix)


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
    """ε-uniform is identity-based (no twins ⇒ ceiling 1); syntactic has its
    DBot/TFT twins (ceiling < 1); behavioral is twin-free on this zoo."""
    from pd_runner.tau.channels import all_families

    fams = all_families(matrix)
    assert fams["epsilon"].ceiling() == pytest.approx(1.0)
    assert fams["behavioral"].ceiling() == pytest.approx(1.0)
    assert fams["syntactic"].ceiling() < 1.0


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
        # Syntactic tops out below 1.0 (twins), but DBot/TFT twins only blur
        # WHO you face, and at the ceiling the true bot still dominates.
        result = run_tournament(matrix, 1.0, 0.5, family=family)
        assert result.family == family.key
        if family.key != "syntactic":
            assert result.cells == base_tournament_cells(matrix)


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


def test_report_shows_the_family_machinery(matrix) -> None:
    """The analysis page must expose all families: radio, table, comparison."""
    from pd_runner.tau.report import build_report

    page = build_report(matrix, alphas=(0.45,))
    assert page.count('type="radio" name="family"') == 3  # one per family
    assert "Channel comparison at matched transparency" in page
    assert "ε-uniform (null control)" in page
    assert "syntactic (codebase)" in page
    # The syntactic twins are named in the family table.
    assert "DBot/TitForTatBot" in page


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

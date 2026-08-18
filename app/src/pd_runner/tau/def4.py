"""Def 4 — tau-NATIVE bots, and the Def-3 vs Def-4 comparison.

.. warning:: **RETRACTED FRAMING (2026-08-13).** The "Def 4 is a LANGUAGE, per-bot
   probe geometry" reading below is OUTDATED AND WRONG. Correct Def 4 is the
   uniform STRUCTURAL SOURCE LIFT: lift A's own code and vote once over compound
   per-hypothesis decisions — under which **Def 4 COINCIDES with Def 3** (large k,
   terminating cells) and no phase-geometry separation exists. The modelled
   TauEBot is the crowd-exploiter, not τ(EBot); every separation summary computed
   here is retracted. Kept as the kernel-check harness for the implemented
   (retracted) zoo. See TAUBOT_TRANSPARENCY_DESIGN.md Part III retraction.

Def 3 (`play.py`) is one fixed LIFT operator: for every base bot `A`,
`τ(A)` votes on the SELF probe `outcome(A, Bᵢ)` — "what would *I* do against
hypothesis Bᵢ". The direction is part of the definition, the hypotheses are
base bots, and the whole thing is stratified (layer 1 reads layer-0 cells).

Def 4 is a LANGUAGE, not an operator: each tau-native bot writes its own guard,
so the probe direction is a per-bot design choice, hypotheses are tau-level,
and genuine fixpoints (a bot's belief about its own tau avatar) are allowed.
The Lean zoo (`engine/PrisonersDilemma/Tau/Defs.lean`) implements four probe
geometries:

    TauDupoc      RECIPROCITY  "does Bᵢ, seeing exactly me, cooperate?"  (proves it)
    TauTFTSim     THIRD PARTY  "does Bᵢ cooperate against TauCooperate?"  (runs it)
    TauTFTPf      THIRD PARTY  "does Bᵢ cooperate against TauCooperate?"  (proves it)
    TauEBot       CASCADE      "exploitable? defect. reciprocates? cooperate."

**The floor (2026-08-12).** A PROVER probe (proofSearch) reads *provable*
cooperation, not true cooperation. EBot's instances cooperate only through a
FAILED exploit-search, so their cooperation certificates pay the `search_f`
floor `> k` and every prover bit on an EBot hypothesis is 0 even where the
cooperation is real (`Tau/Certs.lean: interp_probe_eOfSearch` true +
`ps_probe_eOfSearch_false`). Behavioral (`sim`) probes see TRUE plays and are
floor-blind. An earlier model read the reciprocity bit off the base matrix
(structurally floor-blind for provers) and wrongly gave TauDupoc a provable
EBot bit — caught in review against the base `outcome_DupocBot_vs_EBot = (D,C)`
mechanism.

This module reproduces those probe semantics as matrix arithmetic over the same
certified base matrix, the same `Signal` type, and the same σ family the Def-3
explorer uses — so a side-by-side comparison isolates the PROBE SEMANTICS and
nothing else.

## What is and is not certified

The Lean theorems (`Tau/Phases.lean`) prove the Def-4 plays for LARGE `k`, past
the Löb threshold, and they quantify over arbitrary weights — which is exactly
what lets us instantiate each cell with that matchup's own σ_t signal here.
Below the Löb budget the bits would differ (TauDupoc's self-bit switches off);
that regime is NOT covered by a theorem and is not modelled here. Every table
this module prints is therefore captioned "large k".

## Why the 4-bot control zoo agrees

Self probe and reciprocity probe can only disagree on ASYMMETRIC base cells
(where A's action ≠ B's action). On a zoo whose every cell is symmetric — the
{Dupoc, Coop, Defect, TFT} control — the two definitions induce identical
bit-vectors, hence identical phase diagrams. That agreement is a real result
(a computed anchor between the definitions), but it is uninformative about
whether the definition MATTERS; `asymmetry_report` finds the cells that would
separate them, and adding one such hypothesis to the zoo is what makes the
comparison bite.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum

from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.play import _MASS_TOL
from pd_runner.tau.signal import Signal


class Probe(Enum):
    """The probe geometries a Def-4 bot can use.

    `SELF` is included deliberately: it is the Def-3 direction expressed inside
    the Def-4 language, which makes it the CONTROL for separating the
    probe-direction effect from everything else Def 4 changes.
    """

    SELF = "self"
    """"What do *I* do against Bᵢ?" — `outcome(actor, Bᵢ)`, Def 3's direction."""

    RECIPROCITY = "reciprocity"
    """"What does Bᵢ do against *me*?" — `outcome(Bᵢ, actor)`. TauDupoc."""

    THIRD_PARTY = "third_party"
    """"What does Bᵢ do against a fixed third party?" — TauTFTSim / TauTFTPf."""

    CASCADE = "cascade"
    """Base EBot's exploiter cascade, lifted: defect if the signal's exploitable
    mass reaches α, else cooperate iff its reciprocating mass does. TWO
    thresholded masses, hence a cooperation WINDOW (defection at both ends) —
    the non-monotone α-profile that separates Def 4 from Def 3's one-sided
    thresholds. Matches Lean's nested-`tsearch` `TauEBot` (exploit stage = the
    δ_D column, reciprocity stage = the δ_C column)."""

    CONSTANT = "constant"
    """No probe at all — the bot ignores its signal entirely.

    This is NOT the same as a self-probing bot that happens to have a uniform
    bit-vector. In Lean, `TauCooperate`/`TauDefect` are literally `.const .C` /
    `.const .D` ([Tau/Defs.lean]), so they are α-INDEPENDENT: TauDefect defects
    even at α = 0, where a self-probing bot with an all-zero bit-vector would
    cooperate (mass 0 ≥ 0). Modelling them as probing bots contradicted the
    kernel at exactly that corner — caught by `verify_against_lean`, which is
    why the constant geometry is explicit rather than emergent.
    """


@dataclass(frozen=True)
class Def4Bot:
    """A tau-native bot: a probe geometry plus (for THIRD_PARTY) its referent.

    `name` is the display name. `probe` fixes the guard direction. `referent`
    is the fixed third party the THIRD_PARTY probe measures against — for the
    Lean zoo's two TFTs that is the cooperator, matching base TitForTatBot's
    `.sim .opp (.bot CooperateBot)` guard. `action` is the fixed play of a
    CONSTANT bot.
    """

    name: str
    probe: Probe
    referent: str | None = None
    action: str | None = None
    prover: bool = True
    """True when the probe runs through `proofSearch` (floor-aware: an EBot
    hypothesis's true-but-floor-priced cooperation reads 0). False for
    behavioral `sim` probes, which see TRUE plays and are floor-blind.
    Ignored by CONSTANT bots."""

    def __post_init__(self) -> None:
        if self.probe is Probe.THIRD_PARTY and self.referent is None:
            raise ValueError(f"{self.name}: THIRD_PARTY probe needs a referent")
        if self.probe not in (Probe.THIRD_PARTY,) and self.referent is not None:
            raise ValueError(f"{self.name}: only THIRD_PARTY probes take a referent")
        if self.probe is Probe.CONSTANT and self.action not in ("C", "D"):
            raise ValueError(f"{self.name}: CONSTANT bot needs action 'C' or 'D'")
        if self.probe is not Probe.CONSTANT and self.action is not None:
            raise ValueError(f"{self.name}: only CONSTANT bots take a fixed action")
        if self.probe is Probe.CASCADE and not self.prover:
            raise ValueError(f"{self.name}: the CASCADE geometry is prover-only")


FLOOR_BLOCKED_HYPOTHESES: frozenset[str] = frozenset({"EBot"})
"""Hypotheses whose TRUE cooperation is invisible to prover probes.

EBot's instances cooperate only via a failed exploit-search, so the certificate
pays the `search_f` floor and no budget-k probe can cite it
(`no_provable_botSearcherElse_tail`). The set is structural, not per-cell: base
EBot reaches EVERY cooperation through its else-cascade."""


def probe_bit(
    matrix: TauMatrix,
    bot: Def4Bot,
    actor_base: str,
    hypothesis: str,
) -> bool:
    """Does `bot`'s guard fire on `hypothesis`?

    `actor_base` is the base-zoo bot this tau bot lifts — needed by the SELF
    and RECIPROCITY probes, which mention the actor. The bit is read off the
    certified base matrix: at large `k` the Lean bits coincide with the base
    cells (a shallow instance's provable action IS its action), which is the
    faithfulness claim connecting this arithmetic to `Tau/Certs.lean`.

    A CONSTANT bot has no guard; its bits are meaningless and never consulted
    (`tau_play_def4` short-circuits). We report its fixed action so that
    diagnostics like the bit-vector table still render something truthful.
    """
    if bot.probe is Probe.CONSTANT:
        return bot.action == "C"
    if bot.probe is Probe.CASCADE:
        # the compound point-mass bit: not exploitable AND reciprocating
        return (not _exploit_bit(matrix, bot, hypothesis)) and _recip_bit(
            matrix, bot, hypothesis
        )
    if bot.probe is Probe.SELF:
        raw = matrix.cooperates(actor_base, hypothesis)
    elif bot.probe is Probe.RECIPROCITY:
        raw = matrix.cooperates(hypothesis, actor_base)
    else:
        assert bot.referent is not None
        raw = matrix.cooperates(hypothesis, bot.referent)
    if raw and bot.prover and hypothesis in FLOOR_BLOCKED_HYPOTHESES:
        return False
    return raw


def _exploit_bit(matrix: TauMatrix, bot: Def4Bot, hypothesis: str) -> bool:
    """CASCADE stage 1: does the hypothesis (provably) cooperate with a defector?"""
    raw = matrix.cooperates(hypothesis, "DefectBot")
    if raw and bot.prover and hypothesis in FLOOR_BLOCKED_HYPOTHESES:
        return False
    return raw


def _recip_bit(matrix: TauMatrix, bot: Def4Bot, hypothesis: str) -> bool:
    """CASCADE stage 2: does the hypothesis (provably) cooperate with a cooperator?"""
    raw = matrix.cooperates(hypothesis, "CooperateBot")
    if raw and bot.prover and hypothesis in FLOOR_BLOCKED_HYPOTHESES:
        return False
    return raw


def exploit_mass_def4(
    matrix: TauMatrix,
    bot: Def4Bot,
    signal: Signal,
) -> float:
    """Σ pᵢ over exploitable hypotheses — the CASCADE's first threshold mass."""
    assert bot.probe is Probe.CASCADE
    return math.fsum(
        p
        for hypothesis, p in signal.weights.items()
        if p > 0 and _exploit_bit(matrix, bot, hypothesis)
    )


def threshold_masses(
    matrix: TauMatrix,
    bot: Def4Bot,
    actor_base: str,
    signal: Signal,
) -> tuple[float, ...]:
    """Every mass this bot thresholds against α — the α-breakpoint sources.

    One mass for the single-stage geometries, TWO for the CASCADE (its exploit
    mass is a phase boundary too: crossing it flips the bot from the window
    into low-θ defection)."""
    if bot.probe is Probe.CONSTANT:
        return ()
    if bot.probe is Probe.CASCADE:
        return (
            exploit_mass_def4(matrix, bot, signal),
            coop_mass_def4(matrix, bot, actor_base, signal),
        )
    return (coop_mass_def4(matrix, bot, actor_base, signal),)


def coop_mass_def4(
    matrix: TauMatrix,
    bot: Def4Bot,
    actor_base: str,
    signal: Signal,
) -> float:
    """Σ pᵢ over hypotheses whose probe bit fires — Def 4's cooperation mass.

    Exact (`fsum`) summation, as in `play.coop_mass`: a naive sum is
    order-dependent and can miss an exactly-unanimous mass by an ULP.

    For the CASCADE this is the RECIPROCITY-stage mass (the window's upper
    boundary); the exploit mass is separate (`exploit_mass_def4`).
    """
    if bot.probe is Probe.CASCADE:
        return math.fsum(
            p
            for hypothesis, p in signal.weights.items()
            if p > 0 and _recip_bit(matrix, bot, hypothesis)
        )
    return math.fsum(
        p
        for hypothesis, p in signal.weights.items()
        if p > 0 and probe_bit(matrix, bot, actor_base, hypothesis)
    )


def tau_play_def4(
    matrix: TauMatrix,
    bot: Def4Bot,
    actor_base: str,
    alpha: float,
    signal: Signal,
) -> str:
    """Def-4 play ∈ {"C", "D"}, thresholded at `≥ α` (same convention as Def 3).

    CONSTANT bots bypass the threshold entirely, matching their Lean `.const`
    definitions — in particular TauDefect defects even at α = 0.
    """
    if bot.probe is Probe.CONSTANT:
        assert bot.action is not None
        return bot.action
    if bot.probe is Probe.CASCADE:
        # stage 1: the exploit vote (fires → defect, incl. at α = 0, matching
        # Lean's θ = 0 short-circuit into the outer then-branch `.const D`)
        if exploit_mass_def4(matrix, bot, signal) >= alpha - _MASS_TOL:
            return "D"
        # stage 2: the reciprocity vote
        mass = coop_mass_def4(matrix, bot, actor_base, signal)
        return "C" if mass >= alpha - _MASS_TOL else "D"
    mass = coop_mass_def4(matrix, bot, actor_base, signal)
    return "C" if mass >= alpha - _MASS_TOL else "D"


# ── The milestone-1 control zoo ────────────────────────────────────────────

CONTROL_ZOO: dict[str, Def4Bot] = {
    "DupocBot": Def4Bot("TauDupoc", Probe.RECIPROCITY),
    "CooperateBot": Def4Bot("TauCooperate", Probe.CONSTANT, action="C"),
    "DefectBot": Def4Bot("TauDefect", Probe.CONSTANT, action="D"),
    "TitForTatBot": Def4Bot("TauTFTSim", Probe.THIRD_PARTY, referent="CooperateBot"),
}
"""The 4-bot CONTROL zoo, keyed by the BASE bot each tau bot lifts.

Mirrors the Lean milestone-1 zoo exactly: `TauCooperate`/`TauDefect` are
CONSTANT because Lean defines them as `.const .C` / `.const .D`, which makes
them α-independent. (An earlier version modelled them as self-probing bots with
uniform bit-vectors; that agrees everywhere except α = 0, where a mass-0 bot
would cooperate — `verify_against_lean` caught the disagreement against the
kernel. Keep them CONSTANT.)

**This zoo cannot separate the definitions, by construction** — verified: every
conditional bot's bit-vector is identical under both. Use it as the
anchor/control run; use `SEPARATING_ZOO` for the informative one.
"""

CONTROL_BOTS: tuple[str, ...] = (
    "DupocBot",
    "CooperateBot",
    "DefectBot",
    "TitForTatBot",
)

SEPARATING_ZOO: dict[str, Def4Bot] = {
    **CONTROL_ZOO,
    "EBot": Def4Bot("TauEBot", Probe.CASCADE),
}
"""The control zoo plus EBot — the extension that separates Def 3/Def 4.

Two separations, both honest:

* **The window (structural).** TauEBot thresholds TWO masses (exploit, then
  reciprocity), so its cooperation region is `exploit_mass < α ≤ recip_mass` —
  defection at BOTH ends of the α axis. Def 3's lift of EBot is a single
  one-sided threshold on its outcome row; no Def-3 bot is non-monotone in α.
* **The bits.** Def 3 reads EBot's row as "what does EBot do to B" (it
  cooperates with TFT/Dupoc); Def 4's cascade stages read B's δ_D/δ_C columns.
  And TauDupoc's own EBot bit is 0 under Def 4 (the floor) — for the SAME
  reason base `DupocBot vs EBot = (D, C)`: EBot's real cooperation sits behind
  a failed search and cannot be cited within budget.
"""

SEPARATING_BOTS: tuple[str, ...] = CONTROL_BOTS + ("EBot",)

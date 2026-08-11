"""Def 4 — tau-NATIVE bots, and the Def-3 vs Def-4 comparison.

Def 3 (`play.py`) is one fixed LIFT operator: for every base bot `A`,
`τ(A)` votes on the SELF probe `outcome(A, Bᵢ)` — "what would *I* do against
hypothesis Bᵢ". The direction is part of the definition, the hypotheses are
base bots, and the whole thing is stratified (layer 1 reads layer-0 cells).

Def 4 is a LANGUAGE, not an operator: each tau-native bot writes its own guard,
so the probe direction is a per-bot design choice, hypotheses are tau-level,
and genuine fixpoints (a bot's belief about its own tau avatar) are allowed.
The milestone-1 Lean zoo (`engine/PrisonersDilemma/Tau/Defs.lean`) implements
three probe geometries:

    TauDupoc      RECIPROCITY  "does Bᵢ, seeing exactly me, cooperate?"
    TauTFTSim     THIRD PARTY  "does Bᵢ cooperate against TauCooperate?"  (runs it)
    TauTFTPf      THIRD PARTY  "does Bᵢ cooperate against TauCooperate?"  (proves it)

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

    def __post_init__(self) -> None:
        if self.probe is Probe.THIRD_PARTY and self.referent is None:
            raise ValueError(f"{self.name}: THIRD_PARTY probe needs a referent")
        if self.probe is not Probe.THIRD_PARTY and self.referent is not None:
            raise ValueError(f"{self.name}: only THIRD_PARTY probes take a referent")
        if self.probe is Probe.CONSTANT and self.action not in ("C", "D"):
            raise ValueError(f"{self.name}: CONSTANT bot needs action 'C' or 'D'")
        if self.probe is not Probe.CONSTANT and self.action is not None:
            raise ValueError(f"{self.name}: only CONSTANT bots take a fixed action")


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
    if bot.probe is Probe.SELF:
        return matrix.cooperates(actor_base, hypothesis)
    if bot.probe is Probe.RECIPROCITY:
        return matrix.cooperates(hypothesis, actor_base)
    assert bot.referent is not None
    return matrix.cooperates(hypothesis, bot.referent)


def coop_mass_def4(
    matrix: TauMatrix,
    bot: Def4Bot,
    actor_base: str,
    signal: Signal,
) -> float:
    """Σ pᵢ over hypotheses whose probe bit fires — Def 4's cooperation mass.

    Exact (`fsum`) summation, as in `play.coop_mass`: a naive sum is
    order-dependent and can miss an exactly-unanimous mass by an ULP.
    """
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
    "EBot": Def4Bot("TauEBot", Probe.RECIPROCITY),
}
"""The control zoo plus EBot — the smallest extension that separates Def 3/Def 4.

`DupocBot vs EBot = (D, C)` is the needed shape: an ASYMMETRIC cell under a
CONDITIONAL bot. Under Def 3, TauDupoc's bit for the EBot hypothesis is "what
do I do against EBot" = D (0); under Def 4's reciprocity probe it is "what does
EBot do against me" = C (1). One flipped bit moves TauDupoc's cooperation mass
by that hypothesis's weight, which shifts its α-boundary and makes whole cells
of the outcome matrix differ.
"""

SEPARATING_BOTS: tuple[str, ...] = CONTROL_BOTS + ("EBot",)

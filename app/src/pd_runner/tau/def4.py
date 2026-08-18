"""Def 4 — the uniform SOURCE LIFT, mirrored as matrix-free spec arithmetic.

**This module is the Python twin of the Lean Spec DSL** (`Tau/Spec.lean`, Phase 5 of
`DEF4_TVOTE_ROADMAP.md`). The refined Def 4 (2026-08-18) is:

    TauA(B₁…Bₙ; w⃗, θ) = C   iff   Σ { wᵢ : inst(A, δ_Bᵢ) plays C } ≥ θ

where `inst(A, δ_B)` is base bot A's ENTIRE lifted decision procedure run at point
mass on hypothesis B, and "plays" is the TRUE play, read by evaluation. Every
`proofSearch` lives INSIDE an instance, exactly where the lifted base bot's own code
puts it — never at the vote.

A bot is a `LiftSpec` — an ordered cascade of probe stages plus a default action —
transcribed 1:1 from the Lean `tmplSpec` table. `decide(zoo, A, T)` computes the
compound decision of `inst(A, δ_T)` by walking A's cascade, recursing into the
hypothesis's own instances the same way the Lean compiler does, with two pieces of
proof-theoretic bookkeeping:

* **The floor.** A cooperation reached AFTER a failed `prove` stage carries a
  `search_f` floor in its transcript (`> k`), so it is TRUE but UNPROVABLE at the
  probing budget: `decide` returns `provable=False` and any prove-mode probe of it
  reads 0. This is how base `DupocBot vs EBot = (D, C)` reproduces itself one level
  up, structurally — no stipulated `FLOOR_BLOCKED_HYPOTHESES` set anymore.
* **The quine.** A `prove`-mode SELF-target stage probed at the diagonal (T = A) is
  the Löb fixpoint; at large k bounded Löb closes it (`ps_probe_quine`), so the bit
  is 1 when the stage fires cooperation. Any other diagonal shape is out of the
  modelled fragment and raises.

Everything here is LARGE-k: the Lean phase theorems quantify past the Löb threshold,
and the sub-Löb regime is not modelled (unchanged caveat from milestone 1).

**History.** The previous version of this module modelled the RETRACTED per-bot
probe-geometry reading (reciprocity votes, a per-stage-thresholded cascade — the
"crowd-exploiter"). Under the corrected source lift those geometries are gone:
per-bot content is the spec, the vote is uniform, and **Def 4 coincides with Def 3
at large k on every terminating cell** except the recorded Mirror-branch truncation
(`compare.py` certifies exactly that).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache

from pd_runner.tau.play import _MASS_TOL
from pd_runner.tau.signal import Signal


class Mode(Enum):
    """How a stage consults its probe — the Lean `Mode`."""

    PROVE = "prove"
    """Bounded proof search over the probe atom (a `.search` node). Floor-aware:
    reads 1 only on PROVABLE cooperation."""

    RUN = "run"
    """Execute the probed instance and read its true play (a `.sim`-guarded `.ite`).
    Floor-blind."""


SELF = "<self>"
"""The `Target.self` sentinel: the stage imagines the hypothesis facing ME."""


@dataclass(frozen=True)
class Stage:
    """One probe stage — the Lean `Stage`: consult the hypothesis's instance-vs-
    `target` in `mode`; if it cooperates, commit `fire`; else fall through."""

    mode: Mode
    target: str
    """A template name, or the `SELF` sentinel."""
    fire: str
    """Action committed when the stage fires ("C" or "D")."""


@dataclass(frozen=True)
class LiftSpec:
    """A bot spec — the Lean `Spec`: the cascade plus the fall-through default."""

    stages: tuple[Stage, ...]
    default: str


# ── The zoo table (the Lean `tmplSpec`, transcribed 1:1) ───────────────────────

ZOO6: dict[str, LiftSpec] = {
    "TauCooperate": LiftSpec((), "C"),
    "TauDefect": LiftSpec((), "D"),
    "TauTFTSim": LiftSpec((Stage(Mode.RUN, "TauCooperate", "C"),), "D"),
    "TauTFTPf": LiftSpec((Stage(Mode.PROVE, "TauCooperate", "C"),), "D"),
    "TauDupoc": LiftSpec((Stage(Mode.PROVE, SELF, "C"),), "D"),
    "TauEBot": LiftSpec(
        (Stage(Mode.PROVE, "TauDefect", "D"), Stage(Mode.PROVE, "TauCooperate", "C")),
        "D",
    ),
}

TEMPLATES: tuple[str, ...] = (
    "TauCooperate",
    "TauDefect",
    "TauTFTSim",
    "TauTFTPf",
    "TauDupoc",
    "TauEBot",
)
"""Canonical template order — matches the Lean `order6`
([coop, defect, tftSim, tftPf, dupoc, ebot])."""

BASE_OF: dict[str, str] = {
    "TauCooperate": "CooperateBot",
    "TauDefect": "DefectBot",
    "TauTFTSim": "TitForTatBot",
    "TauTFTPf": "TitForTatBot",
    "TauDupoc": "DupocBot",
    "TauEBot": "EBot",
}
"""Which base bot each template lifts. The two TFT variants are two lift MODALITIES
of the same base strategy (behavioral vs prover) — at large k their bits coincide,
which is the budget-gap claim."""

LEAN_SLOT: dict[str, str] = {
    "TauCooperate": "coop",
    "TauDefect": "defect",
    "TauTFTSim": "tftSim",
    "TauTFTPf": "tftPf",
    "TauDupoc": "dupoc",
    "TauEBot": "ebot",
}
"""Template name → the Lean `Tmpl` constructor, for the kernel bit-table check."""


# ── The compound decision (the Python `inst` + its play, large k) ──────────────


class UnsupportedDiagonal(ValueError):
    """A diagonal (T = A) stage shape outside the modelled fragment: a `run`-mode
    self-probe diverges (Mirror-vs-self), and a `prove`-mode self-probe firing D is
    the anti-diagonal (its fixpoint is the historically INCONSISTENT shape, not a
    Löb cooperation). Neither occurs in the zoo; refusing loudly beats guessing."""


@dataclass(frozen=True)
class Decision:
    """What `inst(A, δ_T)` plays, plus whether a ≤k transcript of that play exists.

    `provable=False` marks a FLOOR-priced play: the cascade path that committed it
    contains a failed `prove` stage, whose `search_f` certificate costs more than
    the whole probing budget. A prove-mode probe of this instance honestly reads 0
    even when `action == "C"` — the Gödelian cells (`interp_probe_eOfSearch` true +
    `ps_probe_eOfSearch_false` in `Tau/Certs.lean`)."""

    action: str
    provable: bool


_MAX_DEPTH = 16
"""Mirror of the Lean `instFuel`: generous for any zoo whose probe nesting is
modest; exceeding it means the spec table has a cycle the quine rule does not cut
(two self-probers — the mutual-quine wall)."""


def decide(A: str, T: str, zoo: dict[str, LiftSpec] | None = None) -> Decision:
    """The compound decision of `inst(A, δ_T)` at large k.

    Walks A's cascade at hypothesis T. Stage bits:

    * `prove` stage, target X: 1 iff `inst(T, δ_X)` PROVABLY cooperates — its
      decision is C and floor-free;
    * `run` stage, target X: 1 iff `inst(T, δ_X)` TRULY cooperates;
    * diagonal self-target (`T == A`, prove, fire C): 1 — bounded Löb closes the
      fixpoint at large k.

    where X = A for a SELF target (the hypothesis seeing ME), else the named
    template.
    """
    if zoo is None:
        return _decide_zoo6(A, T)
    return _decide(A, T, _MAX_DEPTH, _freeze(zoo))


def _freeze(zoo: dict[str, LiftSpec]) -> tuple[tuple[str, LiftSpec], ...]:
    return tuple(sorted(zoo.items()))


@lru_cache(maxsize=None)
def _decide_zoo6(A: str, T: str) -> Decision:
    return _decide(A, T, _MAX_DEPTH, _freeze(ZOO6))


def _decide(
    A: str, T: str, depth: int, frozen: tuple[tuple[str, LiftSpec], ...]
) -> Decision:
    if depth == 0:
        raise UnsupportedDiagonal(
            f"probe nesting exceeded {_MAX_DEPTH} at ({A}, {T}) — the spec table has "
            "a cycle the quine rule does not cut (two self-probers?)"
        )
    zoo = dict(frozen)
    spec = zoo[A]
    failed_prove = False
    for st in spec.stages:
        if st.target == SELF and T == A:
            # the quine diagonal: bounded Löb at large k
            if st.mode is Mode.PROVE and st.fire == "C":
                bit = True
            else:
                raise UnsupportedDiagonal(
                    f"{A}: diagonal stage {st} is outside the modelled fragment"
                )
        else:
            X = A if st.target == SELF else st.target
            sub = _decide(T, X, depth - 1, frozen)
            if st.mode is Mode.PROVE:
                bit = sub.action == "C" and sub.provable
            else:
                bit = sub.action == "C"
        if bit:
            return Decision(st.fire, provable=not failed_prove)
        if st.mode is Mode.PROVE:
            failed_prove = True
    return Decision(spec.default, provable=not failed_prove)


def decision_table(
    zoo: dict[str, LiftSpec] | None = None,
    templates: tuple[str, ...] = TEMPLATES,
) -> dict[str, dict[str, Decision]]:
    """The full compound-decision table: `table[A][T] = decide(A, T)`."""
    return {A: {T: decide(A, T, zoo) for T in templates} for A in templates}


# ── The vote (the Lean `tauPlayer`, over base-bot signals) ─────────────────────


def coop_mass_def4(
    template: str,
    signal: Signal,
    tmpl_of: dict[str, str],
    overrides: dict[tuple[str, str], str] | None = None,
) -> float:
    """Σ pᵢ over hypotheses whose COMPOUND bit fires — Def 4's cooperation mass.

    `signal` weights are keyed by BASE bot names (the σ channel's vocabulary);
    `tmpl_of` maps each base hypothesis to the template that lifts it. `overrides`
    patches individual compound bits (`(A, T) → action`) — used by the coincidence
    certification to attribute divergences to whitelisted cells.
    """
    total = []
    for base_hyp, p in signal.weights.items():
        if p <= 0:
            continue
        T = tmpl_of[base_hyp]
        action = decide(template, T).action
        if overrides and (template, T) in overrides:
            action = overrides[(template, T)]
        if action == "C":
            total.append(p)
    return math.fsum(total)


def tau_play_def4(
    template: str,
    alpha: float,
    signal: Signal,
    tmpl_of: dict[str, str],
    overrides: dict[tuple[str, str], str] | None = None,
) -> str:
    """Def-4 play ∈ {"C", "D"}: ONE vote over compound decisions, thresholded at
    `≥ α` (the same convention as Def 3 — which is the point: under the corrected
    definition the two sides differ ONLY in how the per-hypothesis bit is produced,
    and at large k they coincide).

    Constants short-circuit through the same code path (their compound bits are
    uniform), EXCEPT that a bot with an empty cascade ignores the threshold in the
    Lean (`.const` has no vote) — preserved here: an empty-spec bot plays its
    default at every α, including TauDefect defecting at α = 0.
    """
    zoo6 = ZOO6
    if not zoo6[template].stages and template in ("TauCooperate", "TauDefect"):
        return zoo6[template].default
    mass = coop_mass_def4(template, signal, tmpl_of, overrides)
    return "C" if mass >= alpha - _MASS_TOL else "D"


# ── The comparison zoos (base-bot keyed, as the σ channels are) ────────────────

CONTROL_ZOO: dict[str, str] = {
    "DupocBot": "TauDupoc",
    "CooperateBot": "TauCooperate",
    "DefectBot": "TauDefect",
    "TitForTatBot": "TauTFTSim",
}
"""base bot → the template that lifts it, milestone-1 control zoo. Base TFT maps to
the BEHAVIORAL variant (that is what base TitForTatBot is); the prover variant
appears in bit tables as the budget-gap twin."""

CONTROL_BOTS: tuple[str, ...] = (
    "DupocBot",
    "CooperateBot",
    "DefectBot",
    "TitForTatBot",
)

SEPARATING_ZOO: dict[str, str] = {**CONTROL_ZOO, "EBot": "TauEBot"}
"""Control + EBot. Under the RETRACTED reading this zoo separated the definitions;
under the corrected source lift it must NOT (that inversion is the certification
`compare.py` runs), except at the whitelisted Mirror-truncation cell."""

SEPARATING_BOTS: tuple[str, ...] = CONTROL_BOTS + ("EBot",)

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

    PROVE_EQ = "proveEq"
    """Bounded proof search over a STRUCTURAL IDENTITY atom (`.eq`) — "is the probed
    instance literally this term?". CupodTrollBot's guard shape (2026-08-20). The
    identity is decidable in BOTH directions in `S` (`Pf.eqRefl`/`Pf.eqNeg`), so the
    bit is never in doubt; but a FAILED identity commits via `search_f` and therefore
    floors this player's transcript exactly like a failed `prove` stage."""
    """Execute the probed instance and read its true play (a `.sim`-guarded `.ite`).
    Floor-blind."""


SELF = "<self>"
"""The `Target.self` sentinel: the stage imagines the hypothesis facing ME."""


@dataclass(frozen=True)
class Stage:
    """One probe stage — the Lean `Stage`: consult the hypothesis's instance-vs-
    `target` in `mode`; if the consultation yields `test`, commit `fire`; else fall
    through. `test` mirrors the Lean field added 2026-08-18 (OBot watches for
    defection, GuardianBot proves it); the original zoo tests "C"."""

    mode: Mode
    target: str
    """A template name, or the `SELF` sentinel."""
    test: str
    """The action the consultation is tested against ("C" or "D")."""
    fire: str
    """Action committed when the stage fires ("C" or "D")."""


@dataclass(frozen=True)
class LiftSpec:
    """A bot spec — the Lean `Spec`: the cascade plus the fall-through default."""

    stages: tuple[Stage, ...]
    default: str


# ── The zoo table (the Lean `tmplSpec`, transcribed 1:1) ───────────────────────

TAU_ZOO: dict[str, LiftSpec] = {
    "TauCooperate": LiftSpec((), "C"),
    "TauDefect": LiftSpec((), "D"),
    "TauTFTSim": LiftSpec((Stage(Mode.RUN, "TauCooperate", "C", "C"),), "D"),
    "TauTFTPf": LiftSpec((Stage(Mode.PROVE, "TauCooperate", "C", "C"),), "D"),
    "TauDupoc": LiftSpec((Stage(Mode.PROVE, SELF, "C", "C"),), "D"),
    "TauEBot": LiftSpec(
        (Stage(Mode.RUN, "TauDefect", "C", "D"),
         Stage(Mode.RUN, "TauCooperate", "C", "C")),
        "D",
    ),  # RUN since 2026-08-19: base EBot's cascade is .sim watches, not searches
    "TauJust": LiftSpec((Stage(Mode.PROVE, "TauDupoc", "C", "C"),), "D"),
    "TauOBot": LiftSpec(
        (Stage(Mode.RUN, "TauCooperate", "D", "D"),
         Stage(Mode.RUN, "TauDefect", "D", "D")),
        "C",
    ),
    "TauDBot": LiftSpec((Stage(Mode.RUN, "TauDefect", "C", "D"),), "C"),
    "TauCupodTroll": LiftSpec((Stage(Mode.PROVE_EQ, "TauDupoc", "C", "D"),), "C"),
    "TauGuardian": LiftSpec((Stage(Mode.PROVE, "TauCooperate", "D", "D"),), "C"),
}

TEMPLATES: tuple[str, ...] = (
    "TauCooperate",
    "TauDefect",
    "TauTFTSim",
    "TauTFTPf",
    "TauDupoc",
    "TauEBot",
    "TauJust",
    "TauOBot",
    "TauGuardian",
    "TauDBot",
    "TauCupodTroll",
)
"""Canonical template order — matches the Lean `tauOrder`
([coop, defect, tftSim, tftPf, dupoc, ebot])."""

BASE_OF: dict[str, str] = {
    "TauCooperate": "CooperateBot",
    "TauDefect": "DefectBot",
    "TauTFTSim": "TitForTatBot",
    "TauTFTPf": "TitForTatBot",
    "TauDupoc": "DupocBot",
    "TauEBot": "EBot",
    "TauJust": "JustBot",
    "TauOBot": "OBot",
    "TauGuardian": "GuardianBot",
    "TauDBot": "DBot",
    "TauCupodTroll": "CupodTrollBot",
}
"""Which base bot each template lifts. The two TFT variants are two lift MODALITIES
of the same base strategy (behavioral vs prover). Their bits coincide at large k on
FLOOR-FREE columns only: GuardianBot's floor-priced cooperation (9-zoo, 2026-08-18)
is visible to the sim and invisible to the prover at EVERY k, so the prover twin
carries a PERMANENT whitelisted divergence at the guardian cell — the α-gap as a
bit."""

LEAN_SLOT: dict[str, str] = {
    "TauCooperate": "coop",
    "TauDefect": "defect",
    "TauTFTSim": "tftSim",
    "TauTFTPf": "tftPf",
    "TauDupoc": "dupoc",
    "TauEBot": "ebot",
    "TauJust": "just",
    "TauOBot": "obot",
    "TauGuardian": "guardian",
    "TauDBot": "dbot",
    "TauCupodTroll": "cupodTroll",
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
        return _decide_tauZoo(A, T)
    return _decide(A, T, _MAX_DEPTH, _freeze(zoo))


def _freeze(zoo: dict[str, LiftSpec]) -> tuple[tuple[str, LiftSpec], ...]:
    return tuple(sorted(zoo.items()))


@lru_cache(maxsize=None)
def _decide_tauZoo(A: str, T: str) -> Decision:
    return _decide(A, T, _MAX_DEPTH, _freeze(TAU_ZOO))


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
    floored = False  # a failed prove-stage OR a floored run-consultation en route
    for st in spec.stages:
        if st.target == SELF and T == A:
            # the quine diagonal: bounded Löb at large k
            if st.mode is Mode.PROVE and st.test == "C" and st.fire == "C":
                bit = True
            else:
                raise UnsupportedDiagonal(
                    f"{A}: diagonal stage {st} is outside the modelled fragment"
                )
        else:
            X = A if st.target == SELF else st.target
            sub = _decide(T, X, depth - 1, frozen)
            if st.mode is Mode.PROVE_EQ:
                # SYNTACTIC identity, not behavioral: the guard asks whether the
                # probed instance is literally `inst(T, X)`. In this zoo the probing
                # instance and the probed one are always DIFFERENT compiled cascades
                # (the Lean side proves this by a size argument), so the bit is
                # uniformly False. It becomes interesting only when the named target
                # is itself in the zoo — i.e. when CupodBot lands via `.sys`.
                bit = False
            elif st.mode is Mode.PROVE:
                # "provably plays `test`": true play matches AND its transcript is
                # floor-free (a floor-priced play is invisible to proof search)
                bit = sub.action == st.test and sub.provable
            else:
                # behavioral read: TRUE play, floor-blind — but the RUN embeds the
                # consulted transcript, so a floored sub-run floors THIS player's
                # own transcript (ite_t/ite_f cite the guard run)
                bit = sub.action == st.test
                if not sub.provable:
                    floored = True
        if bit:
            return Decision(st.fire, provable=not floored)
        if st.mode in (Mode.PROVE, Mode.PROVE_EQ):
            floored = True
    return Decision(spec.default, provable=not floored)


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
    tauZoo = TAU_ZOO
    if not tauZoo[template].stages and template in ("TauCooperate", "TauDefect"):
        return tauZoo[template].default
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

FULL_ZOO: dict[str, str] = {
    **SEPARATING_ZOO,
    "JustBot": "TauJust",
    "OBot": "TauOBot",
    "GuardianBot": "TauGuardian",
    "DBot": "TauDBot",
    "CupodTrollBot": "TauCupodTroll",
}
"""The whole 9-template zoo (8 base bots; TitForTatBot carries both TFT variants).
The base matrix is total over these, so the coincidence certification runs on all
81 template cells."""

FULL_BOTS: tuple[str, ...] = SEPARATING_BOTS + (
    "JustBot", "OBot", "GuardianBot", "DBot", "CupodTrollBot",
)

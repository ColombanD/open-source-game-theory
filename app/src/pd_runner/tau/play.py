"""Def 3 — the tau lift of a base bot.

    TauA(α)(signal) = C  iff  Σ { pᵢ : A's action in outcome(A, Bᵢ) = C } ≥ α

*A best-responds to each hypothesis with its own decision procedure, then takes
the weighted vote of its own intended actions.* Deterministic by
expectation-then-threshold derandomization: the uncertainty is integrated out
BEFORE the decision, so there are no probabilistic agents, no measure-theoretic
eval, and no probabilistic Löb.

Two dials, never conflated:
  - t (σ-temperature) is TRANSPARENCY, a property of the signal/environment.
  - α is CAUTION, a property of the agent. It is not transparency.

The probe is the SELF probe `outcome(A, Bᵢ)` — A's own action — not the
reciprocity probe `outcome(Bᵢ, A)`. That choice is what makes this a genuine
lift of A rather than a threshold-reciprocator family; see the design note's
"probe × hypothesis square". Its payoff is the anchor theorem: at t = 0 the
tau tournament reproduces the base matrix exactly.

Tie-breaking is `≥ α` (design note Def 3 and the v1b Lean sketch), so α = 0
means unconditional cooperation.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.signal import Signal


# Cooperation masses are sums of up to |zoo| softmax weights, so an exactly-1
# mass can land an ULP short (summing 12 weights loses ~1e-16). Since α = 1 is
# a boundary the phase diagrams sit directly on, comparing `≥ α` naively would
# flip every unconditional cooperator to D there. `math.fsum` removes the
# summation error; this tolerance absorbs the residual in the weights.
_MASS_TOL = 1e-12


def coop_mass(matrix: TauMatrix, actor: str, signal: Signal) -> float:
    """Σ pᵢ over hypotheses against which `actor` itself plays C.

    Uses exact (`fsum`) summation: the naive sum is order-dependent and can
    miss an exactly-unanimous mass by an ULP.
    """
    return math.fsum(
        p
        for hypothesis, p in signal.weights.items()
        if p > 0 and matrix.cooperates(actor, hypothesis)
    )


def tau_play(
    matrix: TauMatrix,
    actor: str,
    alpha: float,
    signal: Signal,
) -> str:
    """TauA(α)(signal) ∈ {"C", "D"} — Def 3, with `≥ α`.

    The comparison is `≥ α − ε` so that a mass which is exactly α mathematically
    still cooperates after floating-point summation. For exact reasoning about
    the threshold, use `exact_alpha_breakpoints` over a rational signal.
    """
    return "C" if coop_mass(matrix, actor, signal) >= alpha - _MASS_TOL else "D"


@dataclass(frozen=True)
class TauOutcome:
    """One tau-vs-tau match: both sides' actions plus the mass that drove them."""

    row_action: str
    col_action: str
    row_coop_mass: float
    col_coop_mass: float


def tau_match(
    matrix: TauMatrix,
    row: str,
    col: str,
    alpha: float,
    channel: dict[str, Signal],
) -> TauOutcome:
    """Tau(row) vs Tau(col), each seeing a blurred signal of the other.

    Well-founded by construction: each side consults only layer-0 matrix cells
    (base-bot hypotheses, self probe), so there is no mutual tau consultation
    and no bistable fixpoint to break. This is precisely why Def 1 was
    rejected — it recursed with no Löb machinery to ground it.
    """
    row_mass = coop_mass(matrix, row, channel[col])
    col_mass = coop_mass(matrix, col, channel[row])
    return TauOutcome(
        row_action="C" if row_mass >= alpha - _MASS_TOL else "D",
        col_action="C" if col_mass >= alpha - _MASS_TOL else "D",
        row_coop_mass=row_mass,
        col_coop_mass=col_mass,
    )


def alpha_breakpoints(
    matrix: TauMatrix,
    channel: dict[str, Signal],
    quantize: int | None = None,
) -> list[float]:
    """The finitely many α values at which any agent's decision can change.

    Only the achievable cooperation masses matter — between two consecutive
    masses every α gives identical behavior. So a sweep enumerates these
    instead of gridding [0, 1], and the resulting phase diagram is exact
    rather than sampled.

    `quantize` rounds masses to that many decimal places before deduplication,
    which collapses float noise in the softmax weights.
    """
    masses = {0.0}
    for actor in matrix.bots:
        for signal in channel.values():
            m = coop_mass(matrix, actor, signal)
            masses.add(round(m, quantize) if quantize is not None else m)
    return sorted(masses)


def exact_alpha_breakpoints(matrix: TauMatrix, signal: Signal) -> list[Fraction]:
    """Exact subset-sum breakpoints for a RATIONAL signal.

    For hand-built signals with rational weights (the v1b Lean core's `ℚ`
    setting) this gives the breakpoints with no floating point at all, which is
    what makes each phase cell a `decide`-grade theorem.
    """
    weights = {b: Fraction(p).limit_denominator(10**6) for b, p in signal.weights.items()}
    masses = {Fraction(0)}
    for actor in matrix.bots:
        masses.add(
            sum(
                (p for b, p in weights.items() if matrix.cooperates(actor, b)),
                Fraction(0),
            )
        )
    return sorted(masses)

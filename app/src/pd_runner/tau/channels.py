"""σ channel families, all calibrated onto the same transparency dial.

A σ family is (what leaks) × (how it blurs). Every family here exposes the
same interface — `channel(t)` for `t ∈ [0, 1]` — where t is the TARGET
normalized-MI transparency (1 = full, 0 = opaque), found by inverting each
family's own raw knob. That calibration is the point: at matched t the
information RATE is identical across families and only the CONFUSION
STRUCTURE differs, so any outcome difference between two families at the same
t is purely about WHICH bots get confused. ("Cooperation under code blur vs
behavior blur at 40% transparency" is then a fair comparison.)

The three v1 families:

- **behavioral** — softmax over Hamming distance between own-action rows.
  Generative justification: it is the exact Bayes posterior (uniform prior)
  of an observer who watched the bot play every zoo member and misread each
  play independently with probability p — a binary symmetric channel on the
  behavior row, since p^d(1-p)^(n-d) ∝ exp(-d·ln((1-p)/p)) is softmax at
  temperature 1/ln((1-p)/p).
- **epsilon** — σ = (1-ε)·δ_B + ε·uniform. The NULL CONTROL: no similarity
  structure at all, every bot equally confusable with every other. Identity-
  based rather than feature-based, so it has NO twin ceiling (transparency
  reaches 1.0 on any zoo). Differences between it and a feature-based family
  at matched t isolate the effect of confusion structure itself.
- **syntactic** — softmax over normalized AST tree edit distance (`tau.syntax`).
  Partial transparency of the SOURCE — degraded open-source game theory —
  where behavioral σ is really the classical watching-it-play story. Its
  confusion structure INVERTS the behavioral one (Dupoc with Cupod: same tree,
  swapped action leaves, opposite conduct). Upgraded from a constructor-profile
  feature vector on 2026-08-04; that shadow was structure-blind (it made
  DBot/TitForTatBot twins) and scale-sensitive (distance tracked program size).

Recorded upgrade path (design note, "σ family roadmap"): node-masking
generative σ (syntactic), sampling/reputation σ, theorem-library σ,
query-signature σ, behavioral×syntactic mixtures.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable

from pd_runner.tau.matrix import TauMatrix
from pd_runner.tau.signal import (
    Signal,
    behavioral_distance_matrix,
    signal_family_at_temperature,
)

# Raw-knob endpoints for softmax-architecture families (temperature) — the
# same range the behavioral pipeline uses: near-point-mass to near-uniform.
_TEMP_LO, _TEMP_HI = 1e-6, 1e4


def channel_transparency(channel: dict[str, Signal], bots: tuple[str, ...]) -> float:
    """Normalized mutual information of an arbitrary channel, uniform prior.

    The family-agnostic generalization of `signal.transparency`: what fraction
    of the identity uncertainty the signal resolves, whatever produced it.
    """
    prior = 1.0 / len(bots)
    marginal: dict[str, float] = {s: 0.0 for s in bots}
    for b in bots:
        for s, p in channel[b].weights.items():
            marginal[s] += prior * p

    mutual_information = 0.0
    for b in bots:
        for s, p in channel[b].weights.items():
            if p > 0 and marginal[s] > 0:
                mutual_information += prior * p * math.log2(p / marginal[s])

    source_entropy = math.log2(len(bots))
    return mutual_information / source_entropy if source_entropy > 0 else 0.0


@dataclass
class SigmaFamily:
    """A parameterized observation channel, exposed on the [0, 1] MI dial.

    `_channel_at_raw` maps the family's raw knob to a channel, with measured
    transparency MONOTONICALLY DECREASING in the knob over [_raw_lo, _raw_hi]
    (knob at _raw_lo ≈ most informative). `channel(t)`/`raw_for(t)` invert the
    MI scale by bisection, cached per dial value.
    """

    key: str
    label: str
    description: str
    bots: tuple[str, ...]
    _channel_at_raw: Callable[[float], dict[str, Signal]]
    _raw_lo: float
    _raw_hi: float
    # Geometric bisection for knobs spanning decades (temperatures); linear
    # for bounded knobs (ε ∈ [0, 1]).
    _geometric: bool = True
    _raw_cache: dict[float, float] = field(default_factory=dict, repr=False)
    _channel_cache: dict[float, dict[str, Signal]] = field(default_factory=dict, repr=False)

    def transparency_at_raw(self, raw: float) -> float:
        return channel_transparency(self._channel_at_raw(raw), self.bots)

    def ceiling(self) -> float:
        """Max reachable transparency — < 1 iff the family has twins."""
        return self.transparency_at_raw(self._raw_lo)

    def raw_for(self, t: float) -> float:
        """Invert the MI scale: the raw knob whose transparency ≈ t."""
        if not -1e-9 <= t <= 1.0 + 1e-9:
            raise ValueError(f"dial must be in [0, 1], got {t}")
        t = min(max(t, 0.0), 1.0)
        key = round(t, 9)
        cached = self._raw_cache.get(key)
        if cached is not None:
            return cached

        if t <= 0.0:
            raw = self._raw_hi
        elif t >= self.ceiling() - 1e-9:
            raw = self._raw_lo
        else:
            lo, hi = self._raw_lo, self._raw_hi
            for _ in range(200):
                mid = math.sqrt(lo * hi) if self._geometric else (lo + hi) / 2
                if self.transparency_at_raw(mid) > t:
                    lo = mid
                else:
                    hi = mid
                converged = (hi / lo < 1.0 + 1e-4) if self._geometric else (hi - lo < 1e-6)
                if converged:
                    break
            raw = math.sqrt(lo * hi) if self._geometric else (lo + hi) / 2
        self._raw_cache[key] = raw
        return raw

    def channel(self, t: float) -> dict[str, Signal]:
        """The whole channel at dial t, cached — σ_t(B) for every true B."""
        key = round(t, 9)
        cached = self._channel_cache.get(key)
        if cached is None:
            cached = self._channel_at_raw(self.raw_for(t))
            self._channel_cache[key] = cached
        return cached

    def transparency(self, t: float) -> float:
        """MEASURED transparency at dial t (= t up to tolerance, ≤ ceiling)."""
        return channel_transparency(self.channel(t), self.bots)


def behavioral_family(matrix: TauMatrix) -> SigmaFamily:
    distances = behavioral_distance_matrix(matrix)
    return SigmaFamily(
        key="behavioral",
        label="behavioral (plays-like)",
        description=(
            "softmax over Hamming distance between own-action rows — the Bayes "
            "posterior of watching every match through a noisy channel"
        ),
        bots=matrix.bots,
        _channel_at_raw=lambda temp: signal_family_at_temperature(matrix, temp, distances),
        _raw_lo=_TEMP_LO,
        _raw_hi=_TEMP_HI,
        _geometric=True,
    )


def epsilon_family(matrix: TauMatrix) -> SigmaFamily:
    bots = matrix.bots
    n = len(bots)

    def at_raw(eps: float) -> dict[str, Signal]:
        return {
            b: Signal({
                b2: (1.0 - eps if b2 == b else 0.0) + eps / n
                for b2 in bots
            })
            for b in bots
        }

    return SigmaFamily(
        key="epsilon",
        label="ε-uniform (null control)",
        description=(
            "(1-ε)·point-mass + ε·uniform — no similarity structure; every bot "
            "equally confusable, so it isolates the effect of WHICH bots get "
            "confused in the other families"
        ),
        bots=bots,
        _channel_at_raw=at_raw,
        _raw_lo=0.0,
        _raw_hi=1.0,
        _geometric=False,
    )


def syntactic_family(matrix: TauMatrix) -> SigmaFamily:
    from pd_runner.tau.syntax import syntactic_distance_matrix

    distances = syntactic_distance_matrix(matrix)

    def at_raw(temp: float) -> dict[str, Signal]:
        # Same softmax architecture as behavioral, over the code distance —
        # so behavioral-vs-syntactic differences are purely the distance's.
        channel: dict[str, Signal] = {}
        for b in matrix.bots:
            logits = {b2: -distances[(b, b2)] / max(temp, 1e-12) for b2 in matrix.bots}
            peak = max(logits.values())
            unnormalized = {b2: math.exp(v - peak) for b2, v in logits.items()}
            total = sum(unnormalized.values())
            channel[b] = Signal({b2: v / total for b2, v in unnormalized.items()})
        return channel

    return SigmaFamily(
        key="syntactic",
        label="syntactic (AST)",
        description=(
            "softmax over normalized tree edit distance between parsed Prog "
            "terms — partial transparency of the SOURCE (degraded OSGT); "
            "confusion structure inverts the behavioral one"
        ),
        bots=matrix.bots,
        _channel_at_raw=at_raw,
        _raw_lo=_TEMP_LO,
        _raw_hi=_TEMP_HI,
        _geometric=True,
    )


def all_families(matrix: TauMatrix) -> dict[str, SigmaFamily]:
    """The v1 families, keyed by `key`, in presentation order."""
    return {
        f.key: f
        for f in (behavioral_family(matrix), epsilon_family(matrix), syntactic_family(matrix))
    }

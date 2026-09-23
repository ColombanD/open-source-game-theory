"""The σ family: blurred signals over the zoo, parameterized by transparency.

A **signal** is a distribution over the zoo: the receiver is uncertain about
WHICH EXACT PROGRAM the opponent is, but every hypothesis is a real zoo member
with fully-transparent syntax. The blur lives in the weights, never in the
programs — that is what keeps prover bots usable (a corrupted source would be
useless to them; a set of exact candidates is not).

**The public dial is `t ∈ [0, 1]`, and it IS the transparency scale**
(normalized mutual information), oriented the intuitive way:

  t = 1   point mass on B          full transparency   (Critch's OSGT)
  t = 0   ≈ uniform over the zoo   zero transparency   (classical opaque PD)

This is not an ad-hoc reparameterization: `sigma`/`signal_family` invert the
MI scale (via `temperature_for_transparency`) so that dialing t = 0.4 yields a
channel whose MEASURED transparency is 40%. Dial, chart axis, and reported
numbers are all the same quantity. Two caveats:

- On a zoo WITH behavioral twins the scale has a ceiling < 1 (twins are
  unseparable at any blur); dialing above the ceiling clamps to the point
  mass.
- t = 0 maps to a large FINITE softmax temperature, not the exact uniform
  distribution — matching the measured 0% endpoint and keeping the α
  knife-edge phenomenon (see the sweep tests) observable rather than
  idealized away.

Underneath, σ is still a softmax over behavioral distance at a raw
`temperature` (the INTERNAL knob, where 0 = point mass and ∞ = uniform):

    σ(B)[B'] ∝ exp(-d(B, B') / temperature)

with `d` the Hamming distance between the two bots' own action rows in the
outcome matrix — "close" means "plays like". `softmax_signal` and
`transparency` operate at that raw level; everything user-facing takes the
[0, 1] dial.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

from pd_runner.tau.matrix import TauMatrix

# Below this temperature σ is numerically a point mass; we return one exactly
# rather than underflowing exp(-d/t).
_POINT_MASS_T = 1e-9


@dataclass(frozen=True)
class Signal:
    """A distribution over zoo members — the Harsanyi type space.

    `weights` maps bot name to probability; entries sum to 1. Zero-weight bots
    may be omitted.
    """

    weights: dict[str, float]

    def __post_init__(self) -> None:
        total = sum(self.weights.values())
        if not math.isclose(total, 1.0, abs_tol=1e-9):
            raise ValueError(f"signal weights must sum to 1, got {total!r}")
        if any(p < 0 for p in self.weights.values()):
            raise ValueError("signal weights must be non-negative")

    @property
    def support(self) -> tuple[str, ...]:
        return tuple(sorted(b for b, p in self.weights.items() if p > 0))

    def entropy(self) -> float:
        """Shannon entropy in bits."""
        return -sum(p * math.log2(p) for p in self.weights.values() if p > 0)

    @classmethod
    def point_mass(cls, bot: str) -> Signal:
        return cls({bot: 1.0})

    @classmethod
    def uniform(cls, bots: tuple[str, ...]) -> Signal:
        return cls({b: 1.0 / len(bots) for b in bots})


def behavioral_distance_matrix(matrix: TauMatrix) -> dict[tuple[str, str], int]:
    """Hamming distance between bots' own action rows.

    `d(B, B')` counts the opponents against which B and B' play differently.
    Range 0..n. Symmetric, zero on the diagonal — but NOT a metric quotient:
    two distinct programs can be behaviorally identical (d = 0) over this
    sub-zoo, which is exactly the case where blur is undetectable behaviorally.
    """
    dist: dict[tuple[str, str], int] = {}
    rows = {b: matrix.row(b) for b in matrix.bots}
    for a in matrix.bots:
        for b in matrix.bots:
            dist[(a, b)] = sum(1 for x, y in zip(rows[a], rows[b]) if x != y)
    return dist


def behavioral_twins(matrix: TauMatrix) -> list[tuple[str, ...]]:
    """Groups of bots indistinguishable by behavior over this sub-zoo.

    These are the pairs σ can never separate at any temperature, so a
    transparency scale must account for them: even at t → 0 the signal cannot
    be a point mass in the information-theoretic sense if twins exist.
    """
    rows: dict[tuple[str, ...], list[str]] = {}
    for b in matrix.bots:
        rows.setdefault(matrix.row(b), []).append(b)
    return [tuple(sorted(g)) for g in rows.values() if len(g) > 1]


def softmax_signal(
    true_bot: str,
    matrix: TauMatrix,
    temperature: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> Signal:
    """The observer's posterior at a RAW softmax temperature (internal knob).

    At `temperature <= 0` this is the exact point mass δ_{true_bot} (full
    transparency). As temperature grows it flattens toward uniform. User-facing
    code should prefer `sigma`, which takes the [0, 1] transparency dial.
    """
    if temperature < 0:
        raise ValueError(f"temperature must be non-negative, got {temperature}")
    if temperature <= _POINT_MASS_T:
        return Signal.point_mass(true_bot)

    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    # Shift by the minimum (always 0, on the diagonal) for numerical safety.
    logits = {b: -dist[(true_bot, b)] / temperature for b in matrix.bots}
    peak = max(logits.values())
    unnormalized = {b: math.exp(v - peak) for b, v in logits.items()}
    total = sum(unnormalized.values())
    return Signal({b: v / total for b, v in unnormalized.items()})


def signal_family_at_temperature(
    matrix: TauMatrix,
    temperature: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> dict[str, Signal]:
    """The whole channel at one RAW softmax temperature (internal knob)."""
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    return {b: softmax_signal(b, matrix, temperature, dist) for b in matrix.bots}


def sigma(
    true_bot: str,
    matrix: TauMatrix,
    t: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> Signal:
    """σ_t(true_bot) on the transparency dial: t = 1 full, t = 0 opaque.

    `t` is the TARGET normalized-MI transparency; the softmax temperature that
    realizes it is found by inverting the scale. On a zoo with behavioral
    twins, t above the ceiling clamps to the point mass.
    """
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    return softmax_signal(
        true_bot, matrix, temperature_for_transparency(matrix, t, distances=dist), dist
    )


def signal_family(
    matrix: TauMatrix,
    t: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> dict[str, Signal]:
    """σ_t for every possible true opponent — the whole channel at one dial t.

    t = 1 is full transparency (point mass on the truth), t = 0 is opaque
    (≈ uniform). One scale inversion is shared across all the signals.
    """
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    temperature = temperature_for_transparency(matrix, t, distances=dist)
    return signal_family_at_temperature(matrix, temperature, dist)


def transparency(
    matrix: TauMatrix,
    temperature: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> float:
    """Normalized mutual information I(B; σ(B)) / H(B) ∈ [0, 1] — the MEASURE.

    Takes the RAW softmax temperature (internal knob), not the [0, 1] dial:
    this function defines the scale the dial is calibrated against, so it must
    stay at the raw level. What it computes: the fraction of the uncertainty
    about the opponent's identity the signal resolves, assuming a uniform
    prior over the sub-zoo. 0.0 = the signal says nothing.

    **The ceiling is below 1 whenever behavioral twins exist** — no behavioral
    signal can separate bots with identical action rows at ANY temperature. On
    the current 12-bot sub-zoo the ceiling is ≈0.843, with the residual ≈0.157
    being exactly the syntactic information that only a term-reading (Löbian)
    agent can exploit. See `behavioral_twins`.

    This is measured on the SOFTMAX channel throughout, including in the t → 0
    limit: `softmax_signal`'s exact point-mass shortcut at t = 0 would
    otherwise read 1.0 and make the scale discontinuous at zero, comparing an
    identity-by-name signal against a behavioral one. The limit is taken from
    the right instead, so `transparency` is continuous and always describes the
    same object.
    """
    temperature = max(temperature, _POINT_MASS_T * 10)
    channel = signal_family_at_temperature(matrix, temperature, distances)
    bots = matrix.bots
    prior = 1.0 / len(bots)

    # Joint p(b, s) = prior * σ_t(b)[s]; marginal over the observed symbol.
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


# Bisection results keyed by (zoo fingerprint, target): the dial functions
# call this on every σ construction, and a sweep re-requests the same handful
# of targets hundreds of times. The fingerprint is the full behavioral row
# set — two matrices with the same bots but different (e.g. stipulated) cells
# hash differently, as they must, since the rows drive the distances.
_TEMPERATURE_CACHE: dict[tuple, float] = {}


def temperature_for_transparency(
    matrix: TauMatrix,
    target: float,
    tolerance: float = 1e-4,
    max_temperature: float = 1e4,
    distances: dict[tuple[str, str], int] | None = None,
) -> float:
    """Invert the transparency scale: the raw temperature whose MI ≈ target.

    This is the calibration behind the [0, 1] dial: `sigma(…, t)` is
    `softmax_signal` at `temperature_for_transparency(matrix, t)`.
    Transparency is monotonically decreasing in temperature, so a bisection
    suffices. Results are cached per (zoo, target).

    Edge behavior: `target = 0` returns `max_temperature` (a large FINITE
    blur — the exact-uniform limit is unreachable and would idealize away the
    α knife edge); targets at or above the zoo's twin ceiling return 0.0 (the
    point mass).
    """
    # A measured ceiling can exceed 1.0 by float residue (a twin-free zoo reads
    # 1.0000000000000002), and callers naturally feed one back in — so clamp
    # rather than reject a value that is 1.0 for every practical purpose.
    if not -1e-9 <= target <= 1.0 + 1e-9:
        raise ValueError(f"target transparency must be in [0, 1], got {target}")
    target = min(max(target, 0.0), 1.0)
    if target <= 0.0:
        return max_temperature

    key = (
        matrix.bots,
        tuple(matrix.row(b) for b in matrix.bots),
        round(target, 9),
        max_temperature,
    )
    cached = _TEMPERATURE_CACHE.get(key)
    if cached is not None:
        return cached

    if distances is None:
        distances = behavioral_distance_matrix(matrix)

    ceiling = transparency(matrix, _POINT_MASS_T * 10, distances)
    if target >= ceiling - 1e-9:
        _TEMPERATURE_CACHE[key] = 0.0
        return 0.0

    low, high = 1e-6, max_temperature
    for _ in range(200):
        mid = math.sqrt(low * high)  # geometric bisection: t spans decades
        if transparency(matrix, mid, distances) > target:
            low = mid
        else:
            high = mid
        if high / low < 1.0 + tolerance:
            break
    result = math.sqrt(low * high)
    _TEMPERATURE_CACHE[key] = result
    return result

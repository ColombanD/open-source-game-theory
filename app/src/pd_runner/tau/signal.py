"""The σ family: blurred signals over the zoo, parameterized by temperature.

A **signal** is a distribution over the zoo: the receiver is uncertain about
WHICH EXACT PROGRAM the opponent is, but every hypothesis is a real zoo member
with fully-transparent syntax. The blur lives in the weights, never in the
programs — that is what keeps prover bots usable (a corrupted source would be
useless to them; a set of exact candidates is not).

σ_t(B) is a softmax over behavioral distance:

    σ_t(B)[B'] ∝ exp(-d(B, B') / t)

with `d` the Hamming distance between the two bots' own action rows in the
outcome matrix — "close" means "plays like". Computable from data we already
have.

Limits, which are the interpolation story:
  t → 0   point mass on B          full transparency   (Critch's OSGT)
  t → ∞   uniform over the zoo     zero transparency   (classical opaque PD)

Transparency is reported on a principled % scale as normalized mutual
information I(B; σ(B)) / H(B), NOT as raw t — t is unitless and its scale
depends on the zoo size.
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
    """σ_t(true_bot): the observer's posterior over who the opponent is.

    At `temperature <= 0` this is the exact point mass δ_{true_bot} (full
    transparency). As temperature grows it flattens toward uniform.
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


def signal_family(
    matrix: TauMatrix,
    temperature: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> dict[str, Signal]:
    """σ_t for every possible true opponent — the whole channel at one t."""
    dist = distances if distances is not None else behavioral_distance_matrix(matrix)
    return {b: softmax_signal(b, matrix, temperature, dist) for b in matrix.bots}


def transparency(
    matrix: TauMatrix,
    temperature: float,
    distances: dict[tuple[str, str], int] | None = None,
) -> float:
    """Normalized mutual information I(B; σ(B)) / H(B) ∈ [0, 1].

    The principled transparency scale: what fraction of the uncertainty about
    the opponent's identity the signal resolves, assuming a uniform prior over
    the sub-zoo. 0.0 = the signal says nothing.

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
    channel = signal_family(matrix, temperature, distances)
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


def temperature_for_transparency(
    matrix: TauMatrix,
    target: float,
    tolerance: float = 1e-4,
    max_temperature: float = 1e4,
) -> float:
    """Invert the transparency scale: find t with normalized MI ≈ target.

    Transparency is monotonically decreasing in t, so a bisection suffices.
    Useful for sweeping on the interpretable axis ("40% transparency") rather
    than on raw temperature.
    """
    # A measured ceiling can exceed 1.0 by float residue (a twin-free zoo reads
    # 1.0000000000000002), and callers naturally feed one back in — so clamp
    # rather than reject a value that is 1.0 for every practical purpose.
    if not -1e-9 <= target <= 1.0 + 1e-9:
        raise ValueError(f"target transparency must be in [0, 1], got {target}")
    target = min(max(target, 0.0), 1.0)
    distances = behavioral_distance_matrix(matrix)

    ceiling = transparency(matrix, _POINT_MASS_T * 10, distances)
    if target >= ceiling - 1e-9:
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
    return math.sqrt(low * high)

"""Stage (iv): the Moran process — finite populations, stochastic.

Stage (iii) asks where an INFINITE population flows deterministically. Real
populations are finite, and in a finite population drift can carry a type to
extinction even when selection favours it. That gap is the difference between
cooperation being REACHABLE and cooperation being LIKELY.

The frequency-dependent Moran process with exponential fitness: at each step
one individual reproduces (with probability proportional to fitness) and one
dies (uniformly). Population size `M` and selection intensity `beta` are the
two dials — `beta -> 0` is neutral drift, `beta -> inf` is pure selection.

What this stage computes, all in closed form rather than by simulation:

  * FIXATION PROBABILITY rho(i -> j): the chance a single mutant `i` takes
    over a resident population of `j`.
  * The SMALL-MUTATION-LIMIT stationary distribution: when mutations are rare
    enough that fixation resolves before the next one arrives, the population
    is a monoculture almost always, and hops between them form a Markov chain
    on the `N` types. Its stationary distribution is the fraction of TIME
    spent at each type.
  * STOCHASTIC STABILITY: the types carrying the most mass in that limit.

Never implemented in the standalone `egt-osgt-main` repo — its `src/moran/`
was a TODO — so this is new code rather than a port.
"""

from .process import (
    FixationResult,
    fixation_probability,
    fixation_matrix,
    payoff_pair,
)
from .stationary import (
    MoranResult,
    stationary_distribution,
    analyse,
)

__all__ = [
    "FixationResult",
    "fixation_probability",
    "fixation_matrix",
    "payoff_pair",
    "MoranResult",
    "stationary_distribution",
    "analyse",
]

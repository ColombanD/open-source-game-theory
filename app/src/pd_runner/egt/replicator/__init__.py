"""Stage (iii): deterministic replicator dynamics and basins of attraction.

The four earlier stages catalogue the RESTING POINTS of a population — which
monocultures are unbeatable (ESS), who displaces whom (invasion), which
mixtures hold together (faces), what is rational at all (Nash). None of them
says which resting point a population actually REACHES, or from how much of
the state space.

This stage answers that. Integrate

    ẋ_i = x_i · ( (A x)_i − xᵀ A x )

from a starting mix and see where it converges; sample many starts and the
share converging to each attractor is its BASIN. That is what upgrades a face
from "this holds together" to "this one captures 70% of starting conditions".

Never implemented in the standalone `egt-osgt-main` repo — its `src/replicator/`
was a TODO — so this is new code rather than a port.
"""

from .dynamics import (
    Trajectory,
    replicator_field,
    integrate,
    simplex_samples,
)
from .basins import (
    Attractor,
    BasinResult,
    estimate_basins,
)

__all__ = [
    "Trajectory",
    "replicator_field",
    "integrate",
    "simplex_samples",
    "Attractor",
    "BasinResult",
    "estimate_basins",
]

"""Invasion-graph construction and analysis for the OSGT payoff matrix.

Edge convention (strict):  i -> j  iff  A[i, j] >  A[j, j].
Edge convention (weak):    i -> j  iff  A[i, j] >= A[j, j].

The strict graph encodes "rare type-i mutant strictly invades a resident
population of type j". The weak graph differs from the strict graph only
on tied pairs; that difference is exactly the set of pairs where the
Maynard-Smith ESS clause-(b) tiebreaker would have to be consulted.
"""

from .graph import build_strict, build_weak, SUSPECT_CELLS
from .analysis import AnalysisResult, compute_readouts, assign_roles
from .loader import load_numeric_A

__all__ = [
    "build_strict",
    "build_weak",
    "SUSPECT_CELLS",
    "AnalysisResult",
    "compute_readouts",
    "assign_roles",
    "load_numeric_A",
]

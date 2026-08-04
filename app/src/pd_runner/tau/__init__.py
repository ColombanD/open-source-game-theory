"""TauBots — graded transparency over the zoo.

Design note: `engine/PrisonersDilemma/Research/Notes/TAUBOT_TRANSPARENCY_DESIGN.md`.

v1a is the Python explorer: the tau layer under Def 3 is pure matrix
arithmetic, so the whole σ/α sweep runs here over the Lean-verified outcome
matrix. Nothing in this package invokes Lean or an LLM.
"""

from pd_runner.tau.matrix import (
    CERTIFIED_SUB_ZOO,
    CUPOD_STIPULATIONS,
    FULL_CERTIFIED_SUB_ZOO,
    PROVEN_ONLY_SUB_ZOO,
    Cell,
    TauMatrix,
    load_tau_matrix,
)
from pd_runner.tau.channels import (
    SigmaFamily,
    all_families,
    behavioral_family,
    epsilon_family,
    syntactic_family,
)
from pd_runner.tau.signal import (
    Signal,
    behavioral_distance_matrix,
    sigma,
    signal_family,
    softmax_signal,
)
from pd_runner.tau.syntax import (
    bot_ast,
    bot_feature_vectors,
    normalized_tree_distance,
    parse_prog,
    syntactic_distance_matrix,
    syntactic_twins,
    tree_edit_distance,
)
from pd_runner.tau.play import (
    alpha_breakpoints,
    coop_mass,
    tau_play,
)

__all__ = [
    "CERTIFIED_SUB_ZOO",
    "CUPOD_STIPULATIONS",
    "FULL_CERTIFIED_SUB_ZOO",
    "PROVEN_ONLY_SUB_ZOO",
    "Cell",
    "TauMatrix",
    "load_tau_matrix",
    "Signal",
    "SigmaFamily",
    "all_families",
    "behavioral_distance_matrix",
    "behavioral_family",
    "bot_ast",
    "bot_feature_vectors",
    "epsilon_family",
    "normalized_tree_distance",
    "parse_prog",
    "sigma",
    "signal_family",
    "softmax_signal",
    "syntactic_distance_matrix",
    "syntactic_family",
    "syntactic_twins",
    "tree_edit_distance",
    "alpha_breakpoints",
    "coop_mass",
    "tau_play",
]

"""TauBots — graded transparency over the zoo.

Design note: `engine/PrisonersDilemma/Research/Notes/TAUBOTS.md`.

v1a is the Python explorer: the tau layer under Def 3 is pure matrix
arithmetic, so the whole σ/α sweep runs here over the Lean-verified outcome
matrix. Nothing in this package invokes Lean or an LLM.

Import submodules directly (`from pd_runner.tau.matrix import load_tau_matrix`)
— this package deliberately re-exports nothing. The former flat re-export list
was unused by every caller in `src/` and `tests/`, and had silently drifted out
of sync with the package (it never covered `sweep`, `report`, or the Def-4
modules), so it was maintenance surface pretending to be an API.
"""

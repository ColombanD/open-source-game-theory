"""The paper's experiments, from tracked results.

`REPRODUCING.md` at the repository root is the guide. Three commands:

    uv run python -m pd_runner.paper.matrix      # an outcome matrix, each cell with its Lean theorem
    uv run python -m pd_runner.paper.numbers     # every number of the experiments section, from paper_results/
    uv run python -m pd_runner.paper.snapshot    # rebuild paper_results/ from the sweep output (after a re-run)

The sweeps (`scripts/rerun_paper_experiments.sh`) write thousands of files under `generated/egt/runs` and
`generated/egt_fine/*/runs`, which stay out of git. `snapshot` reduces them to the few kilobytes the paper's numbers
are read from, `app/paper_results/`, which IS tracked; `numbers` and the figure generator read only that folder.
"""
from pathlib import Path

RESULTS = Path(__file__).resolve().parents[3] / "paper_results"

# Code name -> the paper's name.
LIBRARIES = {
    "nonprovers+dupoc": "Sigma minus CupodBot (7 programs)",
    "body8": "Sigma (8 programs)",
    "body8+trolls": "Sigma + trolls (10 programs)",
    "body8+trolls+provers": "Sigma + trolls + provers (12 programs)",
}
# The order of the programs in the paper's outcome matrices.
PAPER_ORDER = ["CooperateBot", "DefectBot", "TitForTatBot", "DBot", "OBot", "EBot", "DupocBot", "CupodBot",
               "CupodTrollBot", "DupocTrollBot", "CIMCIC", "DIMDID"]
SIDES = {"engine_side": "negative side of the hinge", "hinge_side": "positive side of the hinge"}

# The games of the full-transparency section: the four libraries on the negative side, Sigma on the positive side.
FULL_TRANSPARENCY_GAMES = [(z, "engine_side") for z in LIBRARIES] + [("body8", "hinge_side")]
# The fine-grid sweeps of the partial-transparency section (`scripts/rerun_paper_experiments.sh`).
PARTIAL_TRANSPARENCY_SWEEPS = ["behavioral_engine_side", "syntactic_engine_side",
                               "behavioral_hinge_side", "syntactic_hinge_side"]

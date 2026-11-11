"""An outcome matrix of the paper, cell by cell, with the Lean theorem behind each cell.

Run from `app/`:

    uv run python -m pd_runner.paper.matrix                                  # library Sigma
    uv run python -m pd_runner.paper.matrix --library body8+trolls+provers   # the twelve programs

Reads the export `generated/sprime_outcome_theorems.json` that `lake exe export_sprime_outcomes` writes from the
tagged theorems of `arith/` (the paper's system S). Prints the matrix, row program's action first, then one line
per pair of programs: the outcome, the budgets it holds at, the theorem and its file. A pair on a hinge has two
outcomes, one per side, and a dichotomy theorem that proves both implications.
"""
from __future__ import annotations

import argparse
import json
import warnings

from pd_runner.eval import outcome_matrix as om
from pd_runner.paper import LIBRARIES, PAPER_ORDER
from pd_runner.tau.matrix import get_zoo, load_tau_matrix

REGIME = {"nobudget": "no budget involved", "universal": "every budget k", "eventual": "all large k"}


def lean_file(module: str) -> str:
    return "arith/" + module.replace(".", "/") + ".lean"


def pairs(library: str) -> list[dict]:
    """One record per unordered pair of the library's programs, in the paper's program order."""
    programs = [p for p in PAPER_ORDER if p in get_zoo(library).bots]
    assert len(programs) == len(get_zoo(library).bots)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        negative = load_tau_matrix(tuple(programs), source="sprime", floor_policy="engine_side")
        positive = load_tau_matrix(tuple(programs), source="sprime", floor_policy="hinge_side")
    export = json.loads(om._EXPORT_FILES["sprime"].read_text())
    record = {t["name"]: t for t in export["theorems"] + export["floors"]}
    out = []
    for i, row in enumerate(programs):
        for col in programs[i:]:
            cell = negative.cell(row, col)
            rec = record[cell.theorem]
            other = positive.cell(row, col)
            out.append({
                "row": row, "col": col,
                "outcome": cell.row_action + cell.col_action,
                "regime": REGIME[rec["budget_regime"]],
                "theorem": cell.theorem, "file": lean_file(rec["module"]),
                "hinge": cell.is_floor,
                "positive_side": other.row_action + other.col_action if cell.is_floor else None,
                "dichotomy": rec.get("dichotomy"),
            })
    return out


def report(library: str) -> str:
    rows = pairs(library)
    programs = [p for p in PAPER_ORDER if p in get_zoo(library).bots]
    value = {}
    for r in rows:
        mark = "‡" if r["hinge"] else " "
        value[(r["row"], r["col"])] = r["outcome"] + mark
        value[(r["col"], r["row"])] = r["outcome"][::-1] + mark
    width = max(len(p) for p in programs)
    L = [f"{LIBRARIES.get(library, library)}: outcomes in S at a shared budget k, row program's action first.",
         "‡ = on a hinge, shown on its negative side.", ""]
    L.append(" " * width + "  " + " ".join(f"{p[:5]:>5s}" for p in programs))
    for r in programs:
        L.append(f"{r:<{width}s}  " + " ".join(f"{value[(r, c)]:>5s}" for c in programs))
    n_hinge = sum(r["hinge"] for r in rows)
    L += ["", f"{len(rows)} pairs of programs: {len(rows) - n_hinge} decided, {n_hinge} on a hinge.", ""]
    for r in rows:
        line = f"{r['row']} x {r['col']}: ({r['outcome'][0]}, {r['outcome'][1]})"
        if r["hinge"]:
            line += (f" on the negative side, ({r['positive_side'][0]}, {r['positive_side'][1]}) on the positive "
                     f"side, {r['regime']}; {r['theorem']} in {r['file']}, both sides by {r['dichotomy']}")
        else:
            line += f", {r['regime']}; {r['theorem']} in {r['file']}"
        L.append(line)
    return "\n".join(L)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--library", default="body8", choices=sorted(LIBRARIES))
    print(report(parser.parse_args().library))


if __name__ == "__main__":
    main()

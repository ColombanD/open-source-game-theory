"""CSV / JSON / Markdown writers for the ESS pipeline."""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import List, Mapping

import numpy as np  # type: ignore

from .ess import EssResult

SUMMARY_COLUMNS = ["type", "is_ESS", "n_invaders", "failing_invaders", "notes"]
PAIRWISE_COLUMNS = [
    "i", "j",
    "A_ii", "A_ji", "A_ij", "A_jj",
    "clause_a_holds", "tie_at_ji", "clause_b_holds",
    "i_survives_j", "touches_suspect_cell",
]


def _fmt_num(x: float) -> str:
    return f"{x:.12g}"


def write_summary_csv(summary, out_path: Path) -> None:
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(SUMMARY_COLUMNS)
        for s in summary:
            w.writerow([
                s.type,
                str(bool(s.is_ESS)),
                int(s.n_invaders),
                "|".join(s.failing_invaders),
                s.notes,
            ])


def write_pairwise_csv(pairwise, out_path: Path) -> None:
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(PAIRWISE_COLUMNS)
        for r in pairwise:
            w.writerow([
                r.i, r.j,
                _fmt_num(r.A_ii), _fmt_num(r.A_ji),
                _fmt_num(r.A_ij), _fmt_num(r.A_jj),
                str(bool(r.clause_a_holds)),
                str(bool(r.tie_at_ji)),
                str(bool(r.clause_b_holds)),
                str(bool(r.i_survives_j)),
                str(bool(r.touches_suspect_cell)),
            ])


def write_payoff_matrix_csv(names: List[str], A: np.ndarray, out_path: Path) -> None:
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow([""] + list(names))
        for i, name in enumerate(names):
            w.writerow([name] + [_fmt_num(float(A[i, j])) for j in range(len(names))])


def write_assumptions_json(assumptions: Mapping, out_path: Path) -> None:
    with open(out_path, "w") as f:
        json.dump(assumptions, f, indent=2)
        f.write("\n")


def write_report_md(
    result: EssResult,
    names: List[str],
    A: np.ndarray,
    assumptions: Mapping,
    out_path: Path,
) -> None:
    pd = assumptions["pd_payoffs"]
    trps = pd["implied_trps"]
    lines: List[str] = []

    lines.append("# Pure-strategy ESS verdict on the OSGT payoff matrix")
    lines.append("")
    lines.append(
        f"PD payoffs: `b={pd['b']}`, `c={pd['c']}` → "
        f"`(T={trps['T']}, R={trps['R']}, P={trps['P']}, S={trps['S']})`. "
        "See `assumptions.json` for the full convention."
    )
    lines.append("")
    lines.append(f"Bot order: {', '.join(names)}.")
    lines.append("")

    ess_types = [s for s in result.summary if s.is_ESS]
    non_ess = [s for s in result.summary if not s.is_ESS]

    lines.append("## Verdict")
    lines.append("")
    if not ess_types:
        lines.append(
            "**No pure ESS exists.** Every type is invaded by at least one other "
            "type under the Maynard-Smith two-condition definition. See "
            "`ess_summary.csv` for per-type detail and the per-non-ESS narrative below."
        )
    else:
        lines.append(
            f"**Pure ESS types ({len(ess_types)} of {len(result.summary)}):** "
            + ", ".join(s.type for s in ess_types)
            + "."
        )
    lines.append("")
    lines.append("| bot | is_ESS | failing_invaders | notes |")
    lines.append("|---|---|---|---|")
    for s in result.summary:
        invs = ", ".join(s.failing_invaders) if s.failing_invaders else "—"
        notes = s.notes if s.notes else "—"
        lines.append(f"| {s.type} | {s.is_ESS} | {invs} | {notes} |")
    lines.append("")

    lines.append("## Why each non-ESS fails")
    lines.append("")
    if not non_ess:
        lines.append("All types are ESS; nothing to explain.")
    else:
        by_pair = {(r.i, r.j): r for r in result.pairwise}
        for s in non_ess:
            lines.append(f"### {s.type}")
            for j_name in s.failing_invaders:
                r = by_pair[(s.type, j_name)]
                if r.tie_at_ji:
                    detail = (
                        f"clause (a): A[{s.type},{s.type}]={r.A_ii:g} "
                        f"== A[{j_name},{s.type}]={r.A_ji:g} (tie); "
                        f"clause (b): A[{s.type},{j_name}]={r.A_ij:g} "
                        f"≤ A[{j_name},{j_name}]={r.A_jj:g}"
                    )
                else:
                    detail = (
                        f"clause (a): A[{s.type},{s.type}]={r.A_ii:g} "
                        f"< A[{j_name},{s.type}]={r.A_ji:g} "
                        f"(no tie, clause (b) inapplicable)"
                    )
                lines.append(
                    f"- invaded by **{j_name}** — {detail}. "
                    f"See `ess_pairwise.csv` (i={s.type}, j={j_name})."
                )
            lines.append("")

    suspect_rows = [r for r in result.pairwise if r.touches_suspect_cell]
    if suspect_rows:
        lines.append("## Flagged input")
        lines.append("")
        lines.append(
            "The following pairwise rows reference the red cell "
            "`(CupodBot, DupocBot)`, which is unresolved in Critch et al. 2022 "
            "and was filled from `config.undefined_outcomes.cupod_vs_dupoc`. "
            "Verdicts that depend on these rows should be regarded as conditional "
            "on the chosen resolution; re-running with the opposite action pair "
            "is planned but not in scope here."
        )
        lines.append("")
        for r in suspect_rows:
            lines.append(
                f"- i={r.i}, j={r.j}: "
                f"A_ii={r.A_ii:g}, A_ji={r.A_ji:g}, "
                f"A_ij={r.A_ij:g}, A_jj={r.A_jj:g}, "
                f"i_survives_j={r.i_survives_j}."
            )
        lines.append("")

    lines.append("## Methodology")
    lines.append("")
    lines.append(
        "Pure-strategy ESS in the Maynard-Smith two-condition form "
        "(Sandholm 2010 Ch. 8; Weibull 1995 Def. 2.1):"
    )
    lines.append("")
    lines.append(
        "> Type *i* is an ESS iff, for every *j* ≠ *i*, "
        "**A[i,i] > A[j,i]** (clause **a**), "
        "or **A[i,i] = A[j,i]** *and* **A[i,j] > A[j,j]** (clause **b**)."
    )
    lines.append("")
    lines.append(
        "The matrix A is not symmetrised; the asymmetric form of both clauses "
        "is used throughout. Equality tolerance: "
        f"`atol = {assumptions['tolerance']['atol']}`."
    )
    lines.append("")

    with open(out_path, "w") as f:
        f.write("\n".join(lines))


def write_all(
    result: EssResult,
    names: List[str],
    A: np.ndarray,
    assumptions: Mapping,
    out_dir: Path,
) -> None:
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    write_summary_csv(result.summary, out_dir / "ess_summary.csv")
    write_pairwise_csv(result.pairwise, out_dir / "ess_pairwise.csv")
    write_payoff_matrix_csv(names, A, out_dir / "payoff_matrix_numeric.csv")
    write_assumptions_json(assumptions, out_dir / "assumptions.json")
    write_report_md(result, names, A, assumptions, out_dir / "report.md")

"""CSV / JSON / Markdown / GEXF writers for the invasion-graph pipeline."""

from __future__ import annotations

import csv
import json
from pathlib import Path
from typing import List, Mapping, Optional

import networkx as nx  # type: ignore
import numpy as np  # type: ignore

from .analysis import AnalysisResult
from .cross_check import VertexAgreement


EDGES_STRICT_COLUMNS = [
    "i", "j", "A_ij", "A_jj", "margin", "touches_suspect_cell",
]
EDGES_WEAK_COLUMNS = [
    "i", "j", "A_ij", "A_jj", "margin", "is_tie", "touches_suspect_cell",
]
TIES_COLUMNS = [
    "i", "j", "A_ij", "A_jj", "A_ji", "A_ii",
    "touches_suspect_cell", "explanation",
]
VERTEX_SUMMARY_COLUMNS = [
    "name", "in_degree", "out_degree", "role",
    "scc_id", "scc_size", "in_terminal_SCC",
    "candidate_ESS_by_clause_a", "is_ESS_per_ess_summary",
    "agrees_with_ess", "responsible_ties", "touches_suspect_cell",
]


def _fmt_num(x: float) -> str:
    return f"{x:.12g}"


def _fmt_bool(x) -> str:
    if x is None:
        return ""
    return str(bool(x))


def write_edges_strict_csv(
    G_strict: nx.DiGraph, A: np.ndarray, out_path: Path
) -> None:
    rows = []
    for u, v, d in G_strict.edges(data=True):
        rows.append({
            "i": G_strict.nodes[u]["name"],
            "j": G_strict.nodes[v]["name"],
            "A_ij": float(A[u, v]),
            "A_jj": float(A[v, v]),
            "margin": float(d["margin"]),
            "touches_suspect_cell": bool(d["touches_suspect_cell"]),
        })
    rows.sort(key=lambda r: (r["i"], r["j"]))
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(EDGES_STRICT_COLUMNS)
        for r in rows:
            w.writerow([
                r["i"], r["j"],
                _fmt_num(r["A_ij"]), _fmt_num(r["A_jj"]),
                _fmt_num(r["margin"]),
                _fmt_bool(r["touches_suspect_cell"]),
            ])


def write_edges_weak_csv(
    G_weak: nx.DiGraph, A: np.ndarray, out_path: Path
) -> None:
    rows = []
    for u, v, d in G_weak.edges(data=True):
        rows.append({
            "i": G_weak.nodes[u]["name"],
            "j": G_weak.nodes[v]["name"],
            "A_ij": float(A[u, v]),
            "A_jj": float(A[v, v]),
            "margin": float(d["margin"]),
            "is_tie": bool(d["is_tie"]),
            "touches_suspect_cell": bool(d["touches_suspect_cell"]),
        })
    rows.sort(key=lambda r: (r["i"], r["j"]))
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(EDGES_WEAK_COLUMNS)
        for r in rows:
            w.writerow([
                r["i"], r["j"],
                _fmt_num(r["A_ij"]), _fmt_num(r["A_jj"]),
                _fmt_num(r["margin"]),
                _fmt_bool(r["is_tie"]),
                _fmt_bool(r["touches_suspect_cell"]),
            ])


def write_ties_csv(
    G_weak: nx.DiGraph, A: np.ndarray, out_path: Path
) -> None:
    rows = []
    for u, v, d in G_weak.edges(data=True):
        if not d["is_tie"]:
            continue
        i_name = G_weak.nodes[u]["name"]
        j_name = G_weak.nodes[v]["name"]
        a_ij = float(A[u, v]); a_jj = float(A[v, v])
        a_ji = float(A[v, u]); a_ii = float(A[u, u])
        explanation = (
            f"A[{i_name},{j_name}]={a_ij:g} == A[{j_name},{j_name}]={a_jj:g} "
            f"(clause (a) tied); clause (b) is decided by comparing "
            f"A[{j_name},{i_name}]={a_ji:g} against A[{i_name},{i_name}]={a_ii:g}."
        )
        rows.append({
            "i": i_name, "j": j_name,
            "A_ij": a_ij, "A_jj": a_jj, "A_ji": a_ji, "A_ii": a_ii,
            "touches_suspect_cell": bool(d["touches_suspect_cell"]),
            "explanation": explanation,
        })
    rows.sort(key=lambda r: (r["i"], r["j"]))
    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(TIES_COLUMNS)
        for r in rows:
            w.writerow([
                r["i"], r["j"],
                _fmt_num(r["A_ij"]), _fmt_num(r["A_jj"]),
                _fmt_num(r["A_ji"]), _fmt_num(r["A_ii"]),
                _fmt_bool(r["touches_suspect_cell"]),
                r["explanation"],
            ])


def write_vertex_summary_csv(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    analysis: AnalysisResult,
    agreements: List[VertexAgreement],
    out_path: Path,
) -> None:
    name_to_v = {G_strict.nodes[v]["name"]: v for v in G_strict.nodes}
    agreement_by_name = {a.name: a for a in agreements}
    scc_size = {s.scc_id: s.size for s in analysis.sccs}
    terminal = set(analysis.terminal_sccs)

    rows = []
    for v in G_strict.nodes:
        name = G_strict.nodes[v]["name"]
        scc_id = analysis.scc_of[v]
        ag = agreement_by_name[name]
        # touches_suspect_cell = any incident edge or tie touches it
        touches = False
        for u, w, d in G_strict.in_edges(v, data=True):
            if d["touches_suspect_cell"]:
                touches = True
                break
        if not touches:
            for u, w, d in G_strict.out_edges(v, data=True):
                if d["touches_suspect_cell"]:
                    touches = True
                    break
        if not touches:
            for u, w, d in G_weak.in_edges(v, data=True):
                if d["touches_suspect_cell"]:
                    touches = True
                    break
        if not touches:
            for u, w, d in G_weak.out_edges(v, data=True):
                if d["touches_suspect_cell"]:
                    touches = True
                    break

        rows.append({
            "name": name,
            "in_degree": int(analysis.in_deg[v]),
            "out_degree": int(analysis.out_deg[v]),
            "role": analysis.roles[v],
            "scc_id": int(scc_id),
            "scc_size": int(scc_size[scc_id]),
            "in_terminal_SCC": scc_id in terminal,
            "candidate_ESS_by_clause_a": ag.candidate_ESS_by_clause_a,
            "is_ESS_per_ess_summary": ag.is_ESS_per_ess_summary,
            "agrees_with_ess": ag.agrees_with_ess,
            "responsible_ties": "|".join(f"{inv}->{vic}" for inv, vic in ag.responsible_ties),
            "touches_suspect_cell": touches,
        })
    rows.sort(key=lambda r: r["name"])

    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(VERTEX_SUMMARY_COLUMNS)
        for r in rows:
            w.writerow([
                r["name"],
                r["in_degree"], r["out_degree"], r["role"],
                r["scc_id"], r["scc_size"], _fmt_bool(r["in_terminal_SCC"]),
                _fmt_bool(r["candidate_ESS_by_clause_a"]),
                _fmt_bool(r["is_ESS_per_ess_summary"]),
                _fmt_bool(r["agrees_with_ess"]),
                r["responsible_ties"],
                _fmt_bool(r["touches_suspect_cell"]),
            ])


def write_sccs_json(analysis: AnalysisResult, out_path: Path) -> None:
    payload = {
        "sccs": [
            {
                "scc_id": s.scc_id,
                "members": list(s.members),
                "member_names": list(s.member_names),
                "size": s.size,
                "is_terminal": s.is_terminal,
                "in_neighbors": list(s.in_neighbors),
                "out_neighbors": list(s.out_neighbors),
            }
            for s in analysis.sccs
        ],
        "condensation_edges": [
            [int(u), int(v)] for u, v in analysis.condensation.edges
        ],
        "topological_order": [int(sid) for sid in analysis.topological_order],
        "terminal_sccs": list(analysis.terminal_sccs),
    }
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")


def write_cycles_json(
    G_strict: nx.DiGraph, analysis: AnalysisResult, out_path: Path
) -> None:
    name = {v: G_strict.nodes[v]["name"] for v in G_strict.nodes}
    cr = analysis.cycles
    payload = {
        "cap": cr.cap,
        "cap_hit": cr.cap_hit,
        "length_bound_if_capped": cr.length_bound_if_capped,
        "n_cycles_total": cr.n_cycles_total,
        "by_length": {
            str(L): [[name[v] for v in cyc] for cyc in cycles]
            for L, cycles in sorted(cr.by_length.items())
        },
        "two_cycles": [[name[u], name[v]] for u, v in cr.two_cycles],
    }
    with open(out_path, "w") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")


def write_cross_check_md(
    G_strict: nx.DiGraph,
    agreements: List[VertexAgreement],
    ess_summary_path: Optional[Path],
    out_path: Path,
) -> None:
    lines: List[str] = []
    lines.append("# Cross-check: invasion graph vs ESS verdict")
    lines.append("")
    if ess_summary_path is None or not Path(ess_summary_path).exists():
        lines.append(
            "No ESS summary CSV provided; reporting clause-(a) candidates only "
            "(`in_degree(G_strict, v) == 0`)."
        )
        lines.append("")
        lines.append("| vertex | candidate_ESS_by_clause_a | responsible_ties |")
        lines.append("|---|---|---|")
        for a in agreements:
            ties = ", ".join(f"{inv}→{vic}" for inv, vic in a.responsible_ties) or "—"
            lines.append(f"| {a.name} | {a.candidate_ESS_by_clause_a} | {ties} |")
        with open(out_path, "w") as f:
            f.write("\n".join(lines) + "\n")
        return

    lines.append(
        "The strict invasion graph captures only clause (a) of Maynard-Smith "
        "ESS, so `in_degree(G_strict, v) == 0` is a NECESSARY (not sufficient) "
        "condition for v to be an ESS. Every pure ESS in `ess_summary.csv` "
        "should therefore appear with in-degree zero; the converse can fail "
        "via clause (b), in which case the responsible tied invader(s) are "
        "listed below."
    )
    lines.append("")
    lines.append("## Agreement table")
    lines.append("")
    lines.append(
        "| vertex | candidate_ESS_by_clause_a | is_ESS_per_ess_summary | "
        "agrees | responsible_ties |"
    )
    lines.append("|---|---|---|---|---|")
    for a in agreements:
        ties = ", ".join(f"{inv}→{vic}" for inv, vic in a.responsible_ties) or "—"
        lines.append(
            f"| {a.name} | {a.candidate_ESS_by_clause_a} | "
            f"{a.is_ESS_per_ess_summary} | {a.agrees_with_ess} | {ties} |"
        )
    lines.append("")

    disagreements = [a for a in agreements if a.agrees_with_ess is False]
    if disagreements:
        lines.append("## Disagreements")
        lines.append("")
        lines.append(
            "Every disagreement below has shape "
            "*clause-(a) candidate that ESS rejects*; the rejection is "
            "mediated by the listed clause-(b) tie(s)."
        )
        lines.append("")
        for a in disagreements:
            ties = ", ".join(f"{inv}→{vic}" for inv, vic in a.responsible_ties) or "—"
            lines.append(
                f"- **{a.name}**: candidate by clause (a) but ESS rejects "
                f"it via tie(s): {ties}. See `ties.csv` rows with "
                f"`j == {a.name}`."
            )
        lines.append("")
    else:
        lines.append("## Disagreements")
        lines.append("")
        lines.append("None. The clause-(a) candidate set matches the ESS verdict exactly.")
        lines.append("")

    # Sanity: every ESS must be a candidate.
    bad = [a for a in agreements
           if a.is_ESS_per_ess_summary and not a.candidate_ESS_by_clause_a]
    if bad:
        lines.append("## Invariant violations")
        lines.append("")
        lines.append(
            "The following vertices are reported as ESS in `ess_summary.csv` "
            "but have strict in-degree > 0; this is impossible under the "
            "Maynard-Smith definition and indicates a pipeline bug:"
        )
        for a in bad:
            lines.append(f"- {a.name}")
        lines.append("")

    with open(out_path, "w") as f:
        f.write("\n".join(lines) + "\n")


def write_report_md(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    analysis: AnalysisResult,
    agreements: List[VertexAgreement],
    A: np.ndarray,
    assumptions: Mapping,
    out_path: Path,
) -> None:
    pd = assumptions.get("pd_payoffs", {})
    trps = pd.get("implied_trps", {})
    lines: List[str] = []
    lines.append("# Invasion graph on the OSGT payoff matrix")
    lines.append("")
    if trps:
        lines.append(
            f"PD payoffs: `b={pd.get('b')}`, `c={pd.get('c')}` → "
            f"`(T={trps.get('T')}, R={trps.get('R')}, "
            f"P={trps.get('P')}, S={trps.get('S')})`. "
            "See `assumptions.json` for the full convention."
        )
        lines.append("")

    names = [G_strict.nodes[v]["name"] for v in sorted(G_strict.nodes)]
    lines.append(f"Vertex set ({len(names)}): {', '.join(names)}.")
    lines.append("")
    n_strict = G_strict.number_of_edges()
    n_weak = G_weak.number_of_edges()
    n_ties = n_weak - n_strict
    lines.append(
        f"Strict edges (G>): **{n_strict}**. "
        f"Weak edges (G≥): **{n_weak}**. "
        f"Tied pairs (clause-(b) territory): **{n_ties}**."
    )
    lines.append("")

    # SCC summary
    lines.append("## Strongly connected components")
    lines.append("")
    lines.append("| scc_id | size | is_terminal | members |")
    lines.append("|---|---|---|---|")
    for s in analysis.sccs:
        lines.append(
            f"| {s.scc_id} | {s.size} | {s.is_terminal} | "
            f"{', '.join(s.member_names)} |"
        )
    lines.append("")
    lines.append(
        f"Condensation has {analysis.condensation.number_of_nodes()} nodes "
        f"and {analysis.condensation.number_of_edges()} edges. Topological "
        f"order: {analysis.topological_order}. Terminal SCCs: "
        f"{analysis.terminal_sccs}. See `sccs.json` for full adjacency."
    )
    lines.append("")

    # Cycles
    cr = analysis.cycles
    lines.append("## Cycles")
    lines.append("")
    lines.append(
        f"Total simple cycles enumerated: **{cr.n_cycles_total}** (cap = {cr.cap}, "
        f"cap_hit = {cr.cap_hit}"
        + (f", length bound applied at L = {cr.length_bound_if_capped}" if cr.cap_hit else "")
        + ")."
    )
    if cr.by_length:
        lines.append("")
        lines.append("Counts by length:")
        for L in sorted(cr.by_length):
            lines.append(f"- length {L}: {len(cr.by_length[L])}")
    lines.append("")
    name = {v: G_strict.nodes[v]["name"] for v in G_strict.nodes}
    if cr.two_cycles:
        lines.append("Two-cycles:")
        for u, v in cr.two_cycles:
            lines.append(f"- {name[u]} ↔ {name[v]}")
        lines.append("")

    # Roles
    lines.append("## Vertex roles")
    lines.append("")
    lines.append("| vertex | in_deg | out_deg | role | scc_id |")
    lines.append("|---|---|---|---|---|")
    for v in sorted(G_strict.nodes, key=lambda x: G_strict.nodes[x]["name"]):
        lines.append(
            f"| {G_strict.nodes[v]['name']} | {analysis.in_deg[v]} | "
            f"{analysis.out_deg[v]} | {analysis.roles[v]} | "
            f"{analysis.scc_of[v]} |"
        )
    lines.append("")

    # Cross-check pointer
    lines.append("## Cross-check with ESS")
    lines.append("")
    n_candidates = sum(1 for a in agreements if a.candidate_ESS_by_clause_a)
    n_ess = sum(1 for a in agreements if a.is_ESS_per_ess_summary)
    n_disagree = sum(1 for a in agreements if a.agrees_with_ess is False)
    lines.append(
        f"Clause-(a) candidates: **{n_candidates}**. "
        f"Pure ESS per `ess_summary.csv`: **{n_ess}**. "
        f"Disagreements (always shape: candidate but not ESS): **{n_disagree}**. "
        "See `cross_check.md` for the per-vertex narrative."
    )
    lines.append("")

    # Suspect cell flag
    suspect_edges = [
        (G_strict.nodes[u]["name"], G_strict.nodes[v]["name"])
        for u, v, d in G_strict.edges(data=True) if d["touches_suspect_cell"]
    ]
    suspect_ties = [
        (G_weak.nodes[u]["name"], G_weak.nodes[v]["name"])
        for u, v, d in G_weak.edges(data=True)
        if d["is_tie"] and d["touches_suspect_cell"]
    ]
    if suspect_edges or suspect_ties:
        lines.append("## Flagged input")
        lines.append("")
        lines.append(
            "The following edges and ties reference the red cell "
            "`(CupodBot, DupocBot)`, which is unresolved in Critch et al. 2022. "
            "Verdicts depending on these should be treated as conditional on "
            "the chosen action-pair resolution."
        )
        if suspect_edges:
            lines.append("")
            lines.append("Strict edges touching the suspect cell:")
            for i, j in suspect_edges:
                lines.append(f"- {i} → {j}")
        if suspect_ties:
            lines.append("")
            lines.append("Tied pairs touching the suspect cell:")
            for i, j in suspect_ties:
                lines.append(f"- {i} ⇢ {j}")
        lines.append("")

    lines.append("## Methodology")
    lines.append("")
    lines.append(
        "Edge convention: `i → j` iff `A[i, j] > A[j, j]` (strict invasion). "
        "Weak invasion: `i →= j` iff `A[i, j] ≥ A[j, j]`. "
        "Equality tolerance: "
        f"`atol = {assumptions.get('tolerance', {}).get('atol', 1e-12)}`. "
        f"Built with `networkx={assumptions.get('library_versions', {}).get('networkx', '?')}`."
    )
    lines.append("")

    with open(out_path, "w") as f:
        f.write("\n".join(lines))


def write_all(
    G_strict: nx.DiGraph,
    G_weak: nx.DiGraph,
    analysis: AnalysisResult,
    agreements: List[VertexAgreement],
    A: np.ndarray,
    assumptions: Mapping,
    ess_summary_path: Optional[Path],
    out_dir: Path,
) -> None:
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    write_edges_strict_csv(G_strict, A, out_dir / "edges_strict.csv")
    write_edges_weak_csv(G_weak, A, out_dir / "edges_weak.csv")
    write_ties_csv(G_weak, A, out_dir / "ties.csv")
    write_vertex_summary_csv(
        G_strict, G_weak, analysis, agreements,
        out_dir / "vertex_summary.csv",
    )
    write_sccs_json(analysis, out_dir / "sccs.json")
    write_cycles_json(G_strict, analysis, out_dir / "cycles.json")
    write_cross_check_md(
        G_strict, agreements, ess_summary_path, out_dir / "cross_check.md"
    )

    nx.write_gexf(G_strict, out_dir / "graph.gexf")
    nx.write_gexf(G_weak, out_dir / "graph_weak.gexf")

    with open(out_dir / "assumptions.json", "w") as f:
        json.dump(assumptions, f, indent=2)
        f.write("\n")

    write_report_md(
        G_strict, G_weak, analysis, agreements, A, assumptions,
        out_dir / "report.md",
    )

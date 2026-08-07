"""IO tests for src/invasion/reporting.py: schemas, GEXF round-trip, OSGT regression."""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT))

import networkx as nx
import numpy as np

from src.invasion.analysis import compute_readouts
from src.invasion.cross_check import compare_against_ess
from src.invasion.graph import SUSPECT_CELLS, build_strict, build_weak
from src.invasion.loader import load_numeric_A
from src.invasion.reporting import (
    EDGES_STRICT_COLUMNS, EDGES_WEAK_COLUMNS, TIES_COLUMNS,
    VERTEX_SUMMARY_COLUMNS, write_all,
)


def _read_csv_rows(path: Path):
    with open(path, newline="") as f:
        reader = csv.reader(f)
        return list(reader)


def test_gexf_roundtrip(tmp_path):
    names = ["a", "b", "c"]
    A = np.array([[2.0, 3.0, 0.0],
                  [0.0, 1.0, 4.0],
                  [3.0, 0.0, 2.0]])
    G = build_strict(names, A)
    out = tmp_path / "g.gexf"
    nx.write_gexf(G, out)
    G2 = nx.read_gexf(out)
    # node attribute preserved (note: GEXF reads node ids as strings)
    names_back = sorted(G2.nodes[n]["name"] for n in G2.nodes)
    assert names_back == ["a", "b", "c"]
    # edge attributes preserved (margin, is_tie, touches_suspect_cell)
    edge_keys = set()
    for u, v, d in G2.edges(data=True):
        edge_keys.update(d.keys())
    assert {"margin", "is_tie", "touches_suspect_cell"} <= edge_keys


def test_osgt_regression(tmp_path):
    """Run the full pipeline on results/ess/payoff_matrix_numeric.csv and
    assert: schema of every CSV, in-degree-zero set ⊇ ESS set."""
    repo = Path(__file__).resolve().parent.parent
    numeric = repo / "results" / "ess" / "payoff_matrix_numeric.csv"
    raw = repo / "data" / "payoff_matrix.csv"
    cfg = repo / "config.json"
    inherited = repo / "results" / "ess" / "assumptions.json"
    ess_sum = repo / "results" / "ess" / "ess_summary.csv"
    assert numeric.exists(), f"missing {numeric}"

    lr = load_numeric_A(numeric, raw, cfg, inherited)
    assert lr.cross_checked, "ingest cross-check must pass"

    G_s = build_strict(lr.bot_names, lr.A, SUSPECT_CELLS)
    G_w = build_weak(lr.bot_names, lr.A, SUSPECT_CELLS)
    res = compute_readouts(G_s, G_w)
    agreements = compare_against_ess(G_s, G_w, ess_sum)

    assumptions = {
        "pd_payoffs": {}, "tolerance": {"atol": 1e-12},
        "library_versions": {"networkx": nx.__version__},
    }
    out = tmp_path / "invasion"
    write_all(G_s, G_w, res, agreements, lr.A, assumptions, ess_sum, out)

    # 1) All expected files exist.
    expected = [
        "edges_strict.csv", "edges_weak.csv", "ties.csv",
        "vertex_summary.csv", "sccs.json", "cycles.json",
        "cross_check.md", "graph.gexf", "graph_weak.gexf",
        "assumptions.json", "report.md",
    ]
    for fn in expected:
        assert (out / fn).exists(), f"missing artefact: {fn}"

    # 2) CSV headers match the documented schemas.
    assert _read_csv_rows(out / "edges_strict.csv")[0] == EDGES_STRICT_COLUMNS
    assert _read_csv_rows(out / "edges_weak.csv")[0] == EDGES_WEAK_COLUMNS
    assert _read_csv_rows(out / "ties.csv")[0] == TIES_COLUMNS
    assert _read_csv_rows(out / "vertex_summary.csv")[0] == VERTEX_SUMMARY_COLUMNS

    # 3) Edge counts: strict ⊆ weak.
    n_strict = len(_read_csv_rows(out / "edges_strict.csv")) - 1
    n_weak = len(_read_csv_rows(out / "edges_weak.csv")) - 1
    assert n_strict <= n_weak

    # 4) Vertex-summary invariant: every ESS appears as in-degree-zero.
    with open(out / "vertex_summary.csv", newline="") as f:
        rows = list(csv.DictReader(f))
    ess_set = {r["name"] for r in rows if r["is_ESS_per_ess_summary"] == "True"}
    candidate_set = {r["name"] for r in rows if r["candidate_ESS_by_clause_a"] == "True"}
    assert ess_set <= candidate_set, "ESS ⊆ clause-(a) candidates must hold"

    # 5) sccs.json is well-formed JSON with the documented keys.
    with open(out / "sccs.json") as f:
        sccs_payload = json.load(f)
    assert {"sccs", "condensation_edges", "topological_order"} <= set(sccs_payload)

    # 6) cycles.json has the documented top-level keys.
    with open(out / "cycles.json") as f:
        cyc = json.load(f)
    assert {"cap", "cap_hit", "n_cycles_total", "by_length", "two_cycles"} <= set(cyc)


def test_load_numeric_A_disagreement_raises(tmp_path):
    """If the numeric CSV diverges from the rebuild, loader must refuse."""
    numeric = tmp_path / "numeric.csv"
    raw = tmp_path / "raw.csv"
    cfg = tmp_path / "config.json"

    # Write a numeric CSV with values that DO NOT correspond to any action
    # pair under the standard PD convention — guaranteed to disagree with
    # any rebuild.
    numeric.write_text("\n".join([
        ",X,Y",
        "X,100,200",
        "Y,300,400",
        "",
    ]))
    # Build a raw action-pair CSV the loader can parse.
    raw.write_text("\n".join([
        ",X,Y",
        'X,"(C, C)","(D, D)"',
        'Y,"(D, D)","(C, C)"',
        "",
    ]))
    cfg.write_text(json.dumps({
        "prisoners_dilemma": {"b": 3.0, "c": 1.0},
        "undefined_outcomes": {"cupod_vs_dupoc": "(C, D)"},
    }))

    import pytest
    with pytest.raises(ValueError, match="disagrees"):
        load_numeric_A(numeric, raw, cfg)

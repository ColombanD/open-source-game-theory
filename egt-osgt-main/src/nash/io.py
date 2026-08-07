"""I/O for the Nash-equilibrium stage.

Writes one self-contained run directory under `results/nash/runs/`:
  equilibria.jsonl          # one extreme NE per line
  equilibria_summary.md     # human-readable table
  nash_components.json      # component grouping
  provenance.json           # run-id, hashes, library versions, timings
  assumptions.json          # mirrors the convention of src/faces/io.py
  dominance_log.json        # iterated strict dominance trace
  verification_report.md    # per-NE pass/fail on original A

A symlink `results/nash/latest -> runs/<run_id>` is updated atomically
after every successful run, and a row is appended to
`results/nash/runs/INDEX.csv`.
"""

from __future__ import annotations

import csv
import datetime as _dt
import hashlib
import importlib.metadata as md
import json
import os
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from src.nash.classification import ClassifiedNE
from src.nash.dominance import DominanceResult
from src.nash.payoff_shift import ShiftRecord
from src.nash.pure_ne import PureNE
from src.nash.reconcile import ReconciledNE
from src.nash.verification import VerifiedNE

NASH_PIPELINE_VERSION = "0.1.0"

# Schema constants — pinned by tests/test_nash_io.py.
EQUILIBRIA_FIELDS: Tuple[str, ...] = (
    "index",
    "support_row",
    "support_col",
    "support_row_names",
    "support_col_names",
    "xi_rational",
    "eta_rational",
    "xi_float",
    "eta_float",
    "u_rational",
    "v_rational",
    "u_float",
    "v_float",
    "cooperation_rate_rational",
    "cooperation_rate_float",
    "classification",
    "asymmetric_pair_id",
    "component_id",
    "discoveries",
    "touches_suspect_cell",
    "verified_on_original_A",
)

INDEX_CSV_HEADER: Tuple[str, ...] = (
    "timestamp",
    "short_hash",
    "run_id",
    "n_extreme_NE",
    "n_components",
    "b",
    "c",
    "undefined_resolution",
    "pygambit_version",
    "lrsnash_version",
    "notes",
)


def _frac_to_str(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def _library_versions(lrsnash_version_str: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for lib in ("pygambit", "numpy", "scipy", "networkx", "pandas"):
        try:
            out[lib] = md.version(lib)
        except Exception:
            pass
    out["lrsnash"] = lrsnash_version_str
    return out


def compute_run_id(
    input_csv_sha: str,
    config: Dict,
    bot_names: List[str],
    pygambit_version: str,
    lrsnash_version_str: str,
    timestamp_utc: _dt.datetime,
) -> Tuple[str, str, str]:
    """Return (run_id, timestamp_str, short_hash). 12-char hex hash."""
    payload = json.dumps(
        {
            "csv_sha": input_csv_sha,
            "b": config["prisoners_dilemma"]["b"],
            "c": config["prisoners_dilemma"]["c"],
            "undefined": config["undefined_outcomes"]["cupod_vs_dupoc"],
            "bots_sorted": sorted(bot_names),
            "pygambit": pygambit_version,
            "lrsnash": lrsnash_version_str,
        },
        sort_keys=True,
    ).encode("utf-8")
    short_hash = hashlib.sha256(payload).hexdigest()[:12]
    ts = timestamp_utc.strftime("%Y%m%dT%H%M%SZ")
    return f"{ts}_{short_hash}", ts, short_hash


def write_equilibria_jsonl(
    records: List[Dict],
    out_path: Path,
) -> None:
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        for rec in records:
            if set(rec.keys()) != set(EQUILIBRIA_FIELDS):
                missing = set(EQUILIBRIA_FIELDS) - set(rec.keys())
                extra = set(rec.keys()) - set(EQUILIBRIA_FIELDS)
                raise ValueError(
                    f"equilibrium record schema mismatch; missing={missing}, extra={extra}"
                )
            f.write(json.dumps(rec) + "\n")


def write_equilibria_summary_md(
    records: List[Dict],
    out_path: Path,
    bot_names: List[str],
) -> None:
    out_path = Path(out_path)
    cols = [
        "idx", "class", "pair", "component",
        "support_row", "support_col",
        "u", "v", "Pr[(C,C)]", "finders",
    ]
    lines = [
        "# Nash equilibria — summary",
        "",
        f"N = {len(bot_names)} bot types: " + ", ".join(bot_names),
        "",
        f"Total extreme NE: **{len(records)}**",
        "",
        "| " + " | ".join(cols) + " |",
        "| " + " | ".join("---" for _ in cols) + " |",
    ]
    for r in records:
        finders = ",".join(sorted({d["finder"] for d in r["discoveries"]}))
        pair_id = r["asymmetric_pair_id"]
        pair_str = "—" if pair_id is None else str(pair_id)
        u = f"{r['u_float']:.4g} ({r['u_rational']})"
        v = f"{r['v_float']:.4g} ({r['v_rational']})"
        coop = f"{r['cooperation_rate_float']:.4g} ({r['cooperation_rate_rational']})"
        sup_r = ",".join(r["support_row_names"]) or "—"
        sup_c = ",".join(r["support_col_names"]) or "—"
        lines.append(
            f"| {r['index']} | {r['classification']} | {pair_str} | {r['component_id']} "
            f"| {sup_r} | {sup_c} | {u} | {v} | {coop} | {finders} |"
        )
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines) + "\n")


def write_components_json(
    components: List[Dict],
    out_path: Path,
) -> None:
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps({"components": components}, indent=2) + "\n")


def write_provenance_json(
    out_path: Path,
    *,
    run_id: str,
    timestamp_utc: str,
    input_csv_path: Path,
    input_csv_sha: str,
    config_path: Path,
    config_resolved: Dict,
    bot_names: List[str],
    shift: ShiftRecord,
    library_versions: Dict[str, str],
    methods_used: List[str],
    dominance: DominanceResult,
    n_extreme_NE: int,
    n_components: int,
    n_pure_NE_direct: int,
    n_pure_NE_in_method2_output: int,
    cross_check_libraries_agree: bool,
    wallclock_seconds: Dict[str, float],
) -> None:
    payload = {
        "run_id": run_id,
        "timestamp_utc": timestamp_utc,
        "input_csv_path": str(input_csv_path),
        "input_csv_sha256": input_csv_sha,
        "config_path": str(config_path),
        "config_resolved": config_resolved,
        "bot_names": bot_names,
        "payoff_shift": {
            "c_shift": _frac_to_str(shift.c_shift),
            "delta": _frac_to_str(shift.delta),
            "min_A_before": _frac_to_str(shift.min_before),
            "min_A_after": _frac_to_str(shift.min_after),
        },
        "library_versions": library_versions,
        "methods_used": methods_used,
        "iterated_dominance": {
            "removed": [
                {
                    "player": r.player,
                    "strategy": r.strategy_name,
                    "dominated_by": r.dominated_by_name,
                    "round": r.round,
                }
                for r in dominance.removals
            ],
            "survivors_row": [bot_names[i] for i in dominance.survivors_row],
            "survivors_col": [bot_names[j] for j in dominance.survivors_col],
        },
        "n_extreme_NE": n_extreme_NE,
        "n_components": n_components,
        "n_pure_NE_direct": n_pure_NE_direct,
        "n_pure_NE_in_method2_output": n_pure_NE_in_method2_output,
        "cross_check_libraries_agree": cross_check_libraries_agree,
        "wallclock_seconds": wallclock_seconds,
    }
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2) + "\n")


def write_assumptions_json(
    out_path: Path,
    *,
    inherited: Optional[Dict],
    bot_names: List[str],
    numeric_matrix_source: Path,
    shift: ShiftRecord,
    library_versions: Dict[str, str],
) -> None:
    pd_payoffs = (inherited or {}).get("pd_payoffs", {})
    excluded = (inherited or {}).get("excluded_types") or {}
    undefined_cells = (inherited or {}).get("undefined_cells_resolved") or {}

    payload = {
        "stage": "nash_equilibria",
        "nash_pipeline_version": NASH_PIPELINE_VERSION,
        "numeric_matrix_source": str(numeric_matrix_source),
        "n_types": len(bot_names),
        "method": "method2_polytope_vertex_enumeration",
        "libraries_used": ["pygambit", "lrsnash"],
        "tolerance": {
            "note": "exact rational arithmetic; no numerical tolerance is used"
        },
        "payoff_shift": {
            "c_shift": _frac_to_str(shift.c_shift),
            "delta": _frac_to_str(shift.delta),
            "rationale": (
                "Method 2 polytope construction requires A > 0 entrywise. "
                "Adding the same constant to both players preserves the NE "
                "set exactly. c_shift is internal; config.json is unchanged."
            ),
        },
        "pd_payoffs": pd_payoffs,
        "bot_names": list(bot_names),
        "excluded_types": excluded,
        "undefined_cells_resolved": undefined_cells,
        "library_versions": library_versions,
    }
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2) + "\n")


def write_dominance_log_json(
    out_path: Path,
    dominance: DominanceResult,
    bot_names: List[str],
) -> None:
    payload = {
        "removed": [
            {
                "player": r.player,
                "strategy": r.strategy_name,
                "dominated_by": r.dominated_by_name,
                "round": r.round,
            }
            for r in dominance.removals
        ],
        "survivors_row": [bot_names[i] for i in dominance.survivors_row],
        "survivors_col": [bot_names[j] for j in dominance.survivors_col],
    }
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2) + "\n")


def write_verification_report_md(
    out_path: Path,
    verified: List[VerifiedNE],
    failures: List,
    n_total: int,
) -> None:
    lines = [
        "# Verification report",
        "",
        f"Extreme NE checked: **{n_total}**",
        f"Passed: **{len(verified)}**",
        f"Failed: **{len(failures)}**",
        "",
    ]
    if failures:
        lines.extend([
            "## Failures",
            "",
            "| ne_index | side | strategy | rel | expected | got |",
            "| --- | --- | --- | --- | --- | --- |",
        ])
        for f in failures:
            lines.append(
                f"| {f.ne_index} | {f.side} | {f.strategy} | {f.rel} | "
                f"{_frac_to_str(f.expected)} | {_frac_to_str(f.got)} |"
            )
        lines.append("")
    else:
        lines.append("_All extreme NE satisfy best-response conditions exactly on the original A._")
        lines.append("")
    Path(out_path).write_text("\n".join(lines))


def append_index_csv(
    index_path: Path,
    *,
    timestamp: str,
    short_hash: str,
    run_id: str,
    n_extreme_NE: int,
    n_components: int,
    b: float,
    c: float,
    undefined_resolution: str,
    pygambit_version: str,
    lrsnash_version_str: str,
    notes: str = "",
) -> None:
    """Append a row to runs/INDEX.csv, creating the file with header if missing."""
    index_path = Path(index_path)
    index_path.parent.mkdir(parents=True, exist_ok=True)
    write_header = not index_path.exists()
    with open(index_path, "a", newline="") as f:
        writer = csv.writer(f)
        if write_header:
            writer.writerow(INDEX_CSV_HEADER)
        writer.writerow([
            timestamp, short_hash, run_id,
            n_extreme_NE, n_components,
            b, c, undefined_resolution,
            pygambit_version, lrsnash_version_str, notes,
        ])


def update_latest_symlink(latest: Path, target_run_dir: Path) -> None:
    """Atomically point `latest` at `target_run_dir`."""
    latest = Path(latest)
    target_rel = os.path.relpath(target_run_dir, latest.parent)
    tmp = latest.parent / (latest.name + ".tmp")
    if tmp.exists() or tmp.is_symlink():
        tmp.unlink()
    os.symlink(target_rel, tmp)
    os.replace(tmp, latest)

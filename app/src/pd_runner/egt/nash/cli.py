"""Entry point: load → shift → enumerate (pygambit + lrsnash) → reconcile →
verify → classify → write all artefacts under results/nash/runs/<run_id>/.

Invoke as:
    conda run -n py-random python -m src.nash.cli \\
        --csv data/payoff_matrix.csv \\
        --config config.json \\
        --numeric-csv results/ess/payoff_matrix_numeric.csv \\
        --inherited-assumptions results/ess/assumptions.json \\
        --out-dir results/nash/
"""

from __future__ import annotations

import argparse
import datetime as _dt
import importlib.metadata as md
import time
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Tuple

from pd_runner.egt.invasion.graph import SUSPECT_CELLS
from pd_runner.egt.nash.classification import classify_all, component_summary
from pd_runner.egt.nash.cooperation import cooperation_rate
from pd_runner.egt.nash.dominance import reduce_iteratively
from pd_runner.egt.nash.game_construction import build_bimatrix
from pd_runner.egt.nash.io import (
    _frac_to_str,
    _library_versions,
    append_index_csv,
    compute_run_id,
    update_latest_symlink,
    write_assumptions_json,
    write_components_json,
    write_dominance_log_json,
    write_equilibria_jsonl,
    write_equilibria_summary_md,
    write_provenance_json,
    write_verification_report_md,
)
from pd_runner.egt.nash.loader import hash_payoff_matrix, load_bundle
from pd_runner.egt.nash.method2_lrsnash import (
    enumerate_lrsnash,
    lrsnash_available,
    lrsnash_version,
)
from pd_runner.egt.nash.method2_pygambit import enumerate_pygambit
from pd_runner.egt.nash.payoff_shift import shift_to_positive
from pd_runner.egt.nash.pure_ne import enumerate_pure
from pd_runner.egt.nash.reconcile import reconcile
from pd_runner.egt.nash.verification import verify_all


def _touches_suspect(
    support_x_names: List[str],
    support_y_names: List[str],
    suspect: Tuple[Tuple[str, str], ...] = SUSPECT_CELLS,
) -> bool:
    for a in support_x_names:
        for b in support_y_names:
            if (a, b) in suspect:
                return True
    return False


def run_pipeline(
    payoff,
    numeric_csv: Path,
    out_dir: Path,
    inherited_assumptions_path: Path | None = None,
    lrsnash_bin: str = "lrsnash",
    lrsnash_timeout_seconds: int = 300,
) -> Path:
    """Execute the full pipeline; return the run directory path.

    `payoff` is the run's `egt.ingest.PayoffMatrix` — it supplies the
    action-pair matrix M (for Pr[(C,C)]) and the cross-check copy of A.

    The lrsnash cross-check is OPTIONAL: lrslib is a system binary that `uv`
    cannot install. When present, the two solvers must agree or the run
    fails; when absent, pygambit runs alone and `cross_check_performed` is
    recorded false. Absence is reported, never silently taken for agreement.
    """
    t_total_start = time.perf_counter()
    bundle = load_bundle(
        payoff=payoff,
        numeric_csv=numeric_csv,
        inherited_assumptions_path=inherited_assumptions_path,
    )
    bot_names = bundle.bot_names
    A_np = bundle.A

    # Shift to positive.
    A_frac, _ = build_bimatrix(A_np)
    A_shifted, shift_rec = shift_to_positive(A_frac)
    B_shifted = [[A_shifted[j][i] for j in range(len(A_shifted))] for i in range(len(A_shifted))]

    # Pure NE direct enumeration (sanity).
    pure_nes = enumerate_pure(A_np)

    # Iterated strict dominance reduction (sanity log).
    dominance = reduce_iteratively(A_np, bot_names)

    # Method 2 enumeration via both libraries.
    t0 = time.perf_counter()
    pygambit_nes = enumerate_pygambit(A_shifted, B_shifted)
    t_pg = time.perf_counter() - t0
    cross_check_performed = lrsnash_available(lrsnash_bin)
    if cross_check_performed:
        t0 = time.perf_counter()
        lrsnash_nes = enumerate_lrsnash(
            A_shifted, B_shifted,
            lrsnash_bin=lrsnash_bin,
            timeout_seconds=lrsnash_timeout_seconds,
        )
        t_lrs = time.perf_counter() - t0

        merged, libraries_agree, sym_diff = reconcile(pygambit_nes, lrsnash_nes)
        if not libraries_agree:
            msg_lines = ["pygambit and lrsnash disagree on the extreme-NE set."]
            for k in sym_diff[:5]:
                msg_lines.append(f"  diff key: {k}")
            if len(sym_diff) > 5:
                msg_lines.append(f"  ... and {len(sym_diff) - 5} more")
            raise AssertionError("\n".join(msg_lines))
    else:
        # No second opinion available. Still go through `reconcile` — it also
        # deduplicates and builds the ReconciledNE records the writers expect;
        # only the agreement CHECK is lost. `libraries_agree` is forced False
        # so the provenance cannot be misread as a passed cross-check (see
        # `cross_check_performed`, which distinguishes the two).
        t_lrs = 0.0
        merged, _, sym_diff = reconcile(pygambit_nes, [])
        libraries_agree = False
        print(
            f"NOTE: {lrsnash_bin!r} not found on PATH — the pygambit/lrsnash "
            "cross-check was SKIPPED for this run. Install lrslib to enable it."
        )

    # Verify every NE on the ORIGINAL A.
    A_frac_for_verify = A_frac  # already Fractions
    verified, failures = verify_all(A_frac_for_verify, merged)
    if failures:
        for fl in failures[:10]:
            print(f"VERIFICATION FAILURE: {fl}")
        raise AssertionError(
            f"{len(failures)} verification failures on original A; see above."
        )
    verified_by_idx = {v.ne_index: (v.u, v.v) for v in verified}

    # Pure-NE round-trip sanity.
    pure_keys = {(p.i, p.j) for p in pure_nes}
    method2_pure_keys = set()
    for idx, ne in enumerate(merged):
        if len(ne.support_x) == 1 and len(ne.support_y) == 1:
            method2_pure_keys.add((ne.support_x[0], ne.support_y[0]))
    missing = pure_keys - method2_pure_keys
    if missing:
        raise AssertionError(
            f"Pure NE missing from Method 2 output: {missing}"
        )

    # Classify symmetry + components.
    classified = classify_all(A_frac, merged)
    components = component_summary(classified)

    # Existence of a symmetric NE.
    if not any(c.classification == "symmetric" for c in classified):
        raise AssertionError(
            "No symmetric NE found — violates Nash 1951 for finite symmetric games."
        )

    # Build per-NE output records.
    records: List[Dict] = []
    for idx in range(len(merged)):
        ne = merged[idx]
        cls = classified[idx]
        u, v = verified_by_idx[idx]
        coop = cooperation_rate(list(ne.xi), list(ne.eta), bundle.M)
        sup_r_names = [bot_names[i] for i in ne.support_x]
        sup_c_names = [bot_names[j] for j in ne.support_y]
        records.append({
            "index": idx,
            "support_row": list(ne.support_x),
            "support_col": list(ne.support_y),
            "support_row_names": sup_r_names,
            "support_col_names": sup_c_names,
            "xi_rational": [_frac_to_str(x) for x in ne.xi],
            "eta_rational": [_frac_to_str(y) for y in ne.eta],
            "xi_float": [float(x) for x in ne.xi],
            "eta_float": [float(y) for y in ne.eta],
            "u_rational": _frac_to_str(u),
            "v_rational": _frac_to_str(v),
            "u_float": float(u),
            "v_float": float(v),
            "cooperation_rate_rational": _frac_to_str(coop),
            "cooperation_rate_float": float(coop),
            "classification": cls.classification,
            "asymmetric_pair_id": cls.asymmetric_pair_id,
            "component_id": cls.component_id,
            "discoveries": [
                {
                    "finder": d.finder,
                    "raw_index": d.raw_index,
                    "label_set_size": d.label_set_size,
                    "component_id": d.component_id,
                }
                for d in ne.discoveries
            ],
            "touches_suspect_cell": _touches_suspect(sup_r_names, sup_c_names),
            "verified_on_original_A": True,
        })

    # Cooperation-rate sanity: any pure (i, i) with M[i][i] == ("C","C") → 1; with ("D","D") → 0.
    for rec in records:
        if len(rec["support_row"]) == 1 and len(rec["support_col"]) == 1:
            i = rec["support_row"][0]
            j = rec["support_col"][0]
            if i == j and bundle.M[i][i] == ("C", "C"):
                if rec["cooperation_rate_rational"] != "1/1":
                    raise AssertionError(
                        f"Pure NE on (C,C) cell {bot_names[i]} has coop != 1: {rec['cooperation_rate_rational']}"
                    )
            if i == j and bundle.M[i][i] == ("D", "D"):
                if rec["cooperation_rate_rational"] != "0/1":
                    raise AssertionError(
                        f"Pure NE on (D,D) cell {bot_names[i]} has coop != 0: {rec['cooperation_rate_rational']}"
                    )

    # Resolve run identity. There is no input CSV any more: the run's
    # fingerprint is the action-pair cells themselves (see hash_payoff_matrix).
    csv_sha = hash_payoff_matrix(payoff)
    lrs_version_str = lrsnash_version(lrsnash_bin) if cross_check_performed else "absent"
    try:
        pygambit_version_str = md.version("pygambit")
    except Exception:
        pygambit_version_str = "unknown"

    timestamp_utc_dt = _dt.datetime.now(_dt.timezone.utc)
    run_id, ts_str, short_hash = compute_run_id(
        input_csv_sha=csv_sha,
        config=bundle.assumptions,
        bot_names=bot_names,
        pygambit_version=pygambit_version_str,
        lrsnash_version_str=lrs_version_str,
        timestamp_utc=timestamp_utc_dt,
    )

    out_dir = Path(out_dir)
    run_dir = out_dir / "runs" / run_id
    run_dir.mkdir(parents=True, exist_ok=True)

    library_versions = _library_versions(lrs_version_str)
    timestamp_iso = timestamp_utc_dt.strftime("%Y-%m-%dT%H:%M:%SZ")
    wallclock = {
        "pygambit": t_pg,
        "lrsnash": t_lrs,
        "total": time.perf_counter() - t_total_start,
    }

    # Write all artefacts.
    write_equilibria_jsonl(records, run_dir / "equilibria.jsonl")
    write_equilibria_summary_md(records, run_dir / "equilibria_summary.md", bot_names)
    write_components_json(components, run_dir / "nash_components.json")
    write_assumptions_json(
        run_dir / "assumptions.json",
        inherited=bundle.inherited_assumptions,
        bot_names=bot_names,
        numeric_matrix_source=bundle.numeric_csv,
        shift=shift_rec,
        library_versions=library_versions,
    )
    write_dominance_log_json(
        run_dir / "dominance_log.json", dominance, bot_names
    )
    write_verification_report_md(
        run_dir / "verification_report.md",
        verified=verified,
        failures=failures,
        n_total=len(merged),
    )
    write_provenance_json(
        run_dir / "provenance.json",
        run_id=run_id,
        timestamp_utc=timestamp_iso,
        input_csv_path=bundle.numeric_csv,
        input_csv_sha=csv_sha,
        config_path=None,
        config_resolved=bundle.assumptions,
        bot_names=bot_names,
        shift=shift_rec,
        library_versions=library_versions,
        methods_used=(
            [
                "pygambit.nash.enummixed_solve(rational=True)",
                "lrsnash",
            ]
            if cross_check_performed
            else ["pygambit.nash.enummixed_solve(rational=True)"]
        ),
        dominance=dominance,
        n_extreme_NE=len(merged),
        n_components=len(components),
        n_pure_NE_direct=len(pure_nes),
        n_pure_NE_in_method2_output=len(method2_pure_keys),
        cross_check_libraries_agree=libraries_agree,
        cross_check_performed=cross_check_performed,
        wallclock_seconds=wallclock,
    )

    # Index + latest pointer.
    pd_payoffs = bundle.assumptions.get("pd_payoffs", {})
    append_index_csv(
        out_dir / "runs" / "INDEX.csv",
        timestamp=ts_str,
        short_hash=short_hash,
        run_id=run_id,
        n_extreme_NE=len(merged),
        n_components=len(components),
        b=pd_payoffs.get("b"),
        c=pd_payoffs.get("c"),
        undefined_resolution=(
            f"zoo={bundle.assumptions.get('zoo')}; "
            f"stipulated={len(bundle.assumptions.get('stipulated_cells', []))}"
        ),
        pygambit_version=pygambit_version_str,
        lrsnash_version_str=lrs_version_str,
    )
    update_latest_symlink(out_dir / "latest", run_dir)

    # Stdout summary.
    print(f"Wrote artefacts to {run_dir}/")
    print(f"  Extreme NE: {len(merged)} (in {len(components)} Nash components)")
    print(f"  Pure NE found directly: {len(pure_nes)}")
    print(f"  Symmetric NE: {sum(1 for c in classified if c.classification == 'symmetric')}")
    print(f"  Asymmetric NE: {sum(1 for c in classified if c.classification == 'asymmetric')}")
    print(f"  pygambit wallclock: {t_pg:.3f}s")
    if cross_check_performed:
        print(f"  lrsnash  wallclock: {t_lrs:.3f}s")
    else:
        print("  lrsnash  cross-check: SKIPPED (binary not on PATH)")
    if dominance.removals:
        print(f"  Iterated strict dominance removed: "
              + ", ".join(f"{r.strategy_name}({r.player})" for r in dominance.removals))
    return run_dir


def main() -> None:
    from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
    from pd_runner.tau.matrix import DEFAULT_ZOO, ZOOS, get_zoo

    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--zoo", default=DEFAULT_ZOO, choices=sorted(ZOOS),
                   help="which tau sub-zoo to analyse (must match the ESS run)")
    p.add_argument(
        "--numeric-csv", type=Path,
        default=Path("generated/egt/ess/payoff_matrix_numeric.csv"),
    )
    p.add_argument(
        "--inherited-assumptions", type=Path,
        default=Path("generated/egt/ess/assumptions.json"),
    )
    p.add_argument("--out-dir", type=Path, default=Path("generated/egt/nash/"))
    p.add_argument("--lrsnash-bin", type=str, default="lrsnash")
    p.add_argument("--lrsnash-timeout-seconds", type=int, default=300)
    args = p.parse_args()

    payoff = payoff_matrix_from_tau_matrix(get_zoo(args.zoo).load(), zoo=args.zoo)

    run_pipeline(
        payoff=payoff,
        numeric_csv=args.numeric_csv,
        inherited_assumptions_path=args.inherited_assumptions,
        out_dir=args.out_dir,
        lrsnash_bin=args.lrsnash_bin,
        lrsnash_timeout_seconds=args.lrsnash_timeout_seconds,
    )


if __name__ == "__main__":
    main()

"""Step 1 of the paper analysis: the INTEGRITY PASS over a finished sweep root.

Reads `runs/*/summary.json` — the per-run summaries, which are complete and
self-describing — never the top-level `sweep_summary*.json` files, because those
are one-per-(family) and each new zoo's sweep into the same root overwrites the
previous zoo's. Checks, in order of severity:

1. **Hard failures** — runs with `ok: false` / non-empty `failed_stages`, and
   per-stage errors. These invalidate the run; nothing downstream may cite it.
2. **Honesty markers** — truncated face enumerations, absent Nash cross-checks
   (expected when `lrsnash` is not installed, but the count belongs in the
   paper's limitations), unconverged replicator trajectories, non-converged
   Moran points, matrices not fully proven.
3. **Anchor checks** — at t = 1 every σ family of a zoo must produce the SAME
   matrix fingerprint (families coincide at point mass), and that fingerprint
   must equal the BASE matrix's (the anchor theorem: the t = 1 tournament
   reproduces the base cells). A mismatch here means the sweep and the paper's
   §5.1 baseline are not talking about the same game.

Exit code: 0 = clean (soft findings allowed), 1 = hard failures or anchor
mismatches. Run with `uv run python -m pd_runner.egt.integrity`.
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

from pd_runner.egt.ingest import payoff_matrix_from_tau_matrix
from pd_runner.egt.pipeline import DEFAULT_OUT_ROOT, cells_fingerprint
from pd_runner.tau.matrix import ZOOS


def load_run_summaries(out_root: Path) -> list[dict]:
    runs = []
    for f in sorted((out_root / "runs").glob("*/summary.json")):
        with f.open() as fh:
            s = json.load(fh)
        s.setdefault("family", "behavioral")  # pre-extension summaries
        s["_dir"] = f.parent
        runs.append(s)
    return runs


def scan_assumptions(run_dir: Path) -> list[str]:
    """Notable entries from every stage's assumptions.json, flattened."""
    notes: list[str] = []
    for f in sorted(run_dir.glob("*/assumptions.json")):
        try:
            data = json.loads(f.read_text())
        except (OSError, json.JSONDecodeError) as e:
            notes.append(f"{f.parent.name}: UNREADABLE assumptions.json ({e})")
            continue
        for key, value in (data.items() if isinstance(data, dict) else []):
            k = key.lower()
            if "truncat" in k and value:
                notes.append(f"{f.parent.name}: {key} = {value!r}")
            if "cross_check" in k and value is False:
                notes.append(f"{f.parent.name}: {key} = False")
    return notes


def main() -> int:
    out_root = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT_ROOT
    runs = load_run_summaries(out_root)
    if not runs:
        print(f"no runs under {out_root / 'runs'}")
        return 1

    hard: list[str] = []
    soft: list[str] = []

    # ── Inventory ─────────────────────────────────────────────────────────
    groups: dict[tuple[str, str], list[dict]] = defaultdict(list)
    for r in runs:
        groups[(r["zoo"], r["family"])].append(r)

    print(f"integrity pass over {out_root}  ({len(runs)} run directories)\n")
    print(f"{'zoo':<14} {'family':<11} {'runs':>4} {'points':>6}  t values / α values")
    for (zoo, family), rs in sorted(groups.items()):
        pts = [tuple(p) for r in rs for p in r["grid_points"]]
        ts = sorted({p[0] for p in pts})
        alphas = sorted({p[1] for p in pts})
        print(f"{zoo:<14} {family:<11} {len(rs):>4} {len(pts):>6}  "
              f"t={ts}  α={alphas}")

    # ── 1. Hard failures ──────────────────────────────────────────────────
    for r in runs:
        if not r.get("ok", False) or r.get("failed_stages"):
            hard.append(f"{r['run']}: ok={r.get('ok')} failed={r.get('failed_stages')}")
        for stage, s in (r.get("stages") or {}).items():
            if s.get("error"):
                hard.append(f"{r['run']}/{stage}: {s['error']}")

    # ── 2. Honesty markers ────────────────────────────────────────────────
    no_cross_check = 0
    for r in runs:
        st = r.get("stages") or {}
        if not r.get("is_fully_proven", True):
            soft.append(f"{r['run']}: matrix NOT fully proven (conditional result)")
        faces = st.get("faces", {})
        if faces and faces.get("enumeration_complete") is False:
            soft.append(f"{r['run']}: face enumeration TRUNCATED")
        nash = st.get("nash", {})
        if nash and nash.get("cross_check_performed") is False:
            no_cross_check += 1
        repl = st.get("replicator", {})
        if repl and repl.get("n_unconverged", 0):
            soft.append(f"{r['run']}: replicator n_unconverged = {repl['n_unconverged']}")
        moran = st.get("moran", {})
        if moran and moran.get("all_converged") is False:
            soft.append(f"{r['run']}: Moran stationary distribution not converged")
        for note in scan_assumptions(r["_dir"]):
            line = f"{r['run']}/{note}"
            if "cross_check" in note:
                continue  # counted above
            soft.append(line)
    if no_cross_check:
        soft.append(f"[expected] Nash cross-check absent (lrsnash not installed) in "
                    f"{no_cross_check}/{len(runs)} runs — record in limitations")

    # ── 3. Anchor checks ──────────────────────────────────────────────────
    print("\nanchor checks (t = 1):")
    anchor_ok = True
    zoos = sorted({z for z, _ in groups})
    for zoo in zoos:
        fps: dict[str, str] = {}
        for (z, family), rs in groups.items():
            if z != zoo:
                continue
            # α = 0 is EXCLUDED by design, not leniency: `≥ α` at α = 0 makes
            # every tau player an unconditional cooperator, so the t=1, α=0
            # matrix is the all-C matrix, not the base matrix. The anchor
            # theorem is about α ∈ (0, 1].
            t1 = [r for r in rs
                  if any(p[0] == 1.0 and p[1] > 0.0 for p in r["grid_points"])]
            if t1:
                fps[family] = "/".join(sorted({r["fingerprint"] for r in t1}))
        if not fps:
            print(f"  {zoo}: no t=1 runs found")
            continue
        try:
            base_fp = cells_fingerprint(
                payoff_matrix_from_tau_matrix(ZOOS[zoo].load(), zoo=zoo))
        except KeyError:
            base_fp = "?"  # zoo no longer registered
        agree = len(set(fps.values())) == 1 and (base_fp in ("?", *fps.values()))
        anchor_ok &= agree
        mark = "OK " if agree else "MISMATCH"
        print(f"  {mark} {zoo}: base={base_fp}  " +
              "  ".join(f"{fam}={fp}" for fam, fp in sorted(fps.items())))

    # ── Report ────────────────────────────────────────────────────────────
    print(f"\nhard failures: {len(hard)}")
    for line in hard:
        print(f"  ✗ {line}")
    print(f"soft findings: {len(soft)}")
    for line in soft:
        print(f"  ⚠ {line}")
    clean = not hard and anchor_ok
    print("\nVERDICT:", "CLEAN — safe to analyse" if clean
          else "NOT CLEAN — resolve hard failures / anchor mismatches first")
    return 0 if clean else 1


if __name__ == "__main__":
    raise SystemExit(main())

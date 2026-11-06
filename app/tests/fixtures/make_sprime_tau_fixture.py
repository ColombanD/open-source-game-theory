"""Build `sprime_tau_rows.sample.json` (+ a PARTIAL twin) — stand-ins for the `S'` tau export.

The real file, `app/generated/sprime_tau_rows.json`, is written by
`lake exe export_sprime_outcomes` from the `@[tau_rowA]`/`@[tau_floor_bitA]` theorems in
`arith/ArithS/Tau/` (`SPRIME_SOURCE_OF_TRUTH.md` §3, Phase 3). Until that exporter has run
the test-suite needs a document in the same schema, so this script derives one from the
`S'` BASE cells (`app/generated/sprime_outcome_theorems.json`) by the very rule the §3
table was derived with — a tau bit at point mass IS the base cell (Def 3 ≡ Def 4):

* the bit at `(A, T)` is the `S'` base cell's A-action for the base bot of template `A`
  against the base bot of template `T` (`BASE_OF`; the natives `maxconfidence` /
  `minconfidence` use `DupocBot` on both axes);
* a FLOOR base cell gives a FLOOR BIT (`floor_bits`: template, slot, engine-side action,
  the cell's hinge and `dich_` name); every other cell is a row slot in `bits`;
* a row's `order` is the literal list of its non-floor slots printed as Lean text
  (`"[coop, defect, …]"`, the contract's "`paperOrder` minus the template's floor
  slots", as the real exporter prints it); the top-level `order` is `paperOrder`. A
  floor bit also carries its theorem `name` (`<t>RowSpecA_<T>_floor`) and `module`.
  The sample's hinge is the BASE cell's; the real export states the hinge on the
  compiled instance (`instCode`), which the loader carries verbatim and no consumer
  compares across the two documents.

Expected content (§3): 196 bits = 155 row slots + 41 floor bits. The digest is FNV-1a over
`rows ++ floor_bits` (each row `json.dumps(sort_keys, compact, ensure_ascii=False)`),
the engine's algorithm. The PARTIAL sample keeps two rows (`dupoc`, `ebot`) with their
floor bits and drops every other template, to exercise the rollout behaviour
(`TauMatrix.kernel_coverage`, `is_kernel_backed` False, loads still total).

Run (from `app/`): `uv run python tests/fixtures/make_sprime_tau_fixture.py`
and commit the regenerated samples.
"""

from __future__ import annotations

import json
import sys
from collections.abc import Sequence
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
BASE_EXPORT = WORKSPACE / "app" / "generated" / "sprime_outcome_theorems.json"
BASE_SAMPLE = HERE / "sprime_outcome_theorems.sample.json"
OUT = HERE / "sprime_tau_rows.sample.json"
OUT_PARTIAL = HERE / "sprime_tau_rows.partial.sample.json"

PARTIAL_TEMPLATES: tuple[str, ...] = ("dupoc", "ebot")
"""The two rows the partial sample keeps (both carry floor bits)."""


def base_export() -> Path:
    """The real `S'` base export, else the Phase-1 ledger-derived sample."""
    return BASE_EXPORT if BASE_EXPORT.exists() else BASE_SAMPLE


def build(export: Path | None = None, templates: Sequence[str] | None = None) -> dict:
    """The document. `templates` (Lean slot names) restricts the ROWS kept — the
    hypothesis axis always runs over the whole `paperOrder`."""
    sys.path.insert(0, str(WORKSPACE / "app" / "src"))
    from pd_runner.eval.outcome_matrix import (
        _fnv1a64,
        index_by_ordered_pair,
        oriented_pair,
        scan_outcome_theorems,
    )
    from pd_runner.tau.def4_theorems import BASE_OF, LEAN_SLOT, PAPER_ORDER, PAPER_TEMPLATES

    cells = scan_outcome_theorems(export_file=export or base_export(), floor_policy="engine_side")
    by_pair = index_by_ordered_pair(cells)
    template_of_slot = {LEAN_SLOT[t]: t for t in PAPER_TEMPLATES}
    keep = set(templates) if templates is not None else set(PAPER_ORDER)

    rows: list[dict] = []
    floor_bits: list[dict] = []
    for slot_a in PAPER_ORDER:
        if slot_a not in keep:
            continue
        tmpl_a = template_of_slot[slot_a]
        base_a = BASE_OF[tmpl_a]
        bits: dict[str, str] = {}
        order: list[str] = []
        for slot_t in PAPER_ORDER:
            base_t = BASE_OF[template_of_slot[slot_t]]
            t = by_pair.get((base_a, base_t)) or by_pair.get((base_t, base_a))
            if t is None:
                raise ValueError(f"no S' cell for ({base_a}, {base_t}) — the paper zoo is not total")
            pair = oriented_pair(t, base_a)
            if pair is None:
                raise ValueError(f"({base_a}, {base_t}) is a proven `none`; no tau bit")
            action = pair[0]
            if t.is_floor:
                floor_bits.append({
                    "template": slot_a,
                    "slot": slot_t,
                    "name": f"{slot_a}RowSpecA_{slot_t}_floor",
                    "module": f"ArithS.Tau.Rows.{tmpl_a[len('Tau'):]}",
                    "hinge": t.hinge,
                    "dichotomy": t.dichotomy or f"dich_{t.left_bot}_vs_{t.right_bot}",
                    "action": action,
                })
            else:
                bits[slot_t] = action
                order.append(slot_t)
        rows.append({
            "template": slot_a,
            # the exporter prints the literal order list as Lean text
            "order": "[" + ", ".join(order) + "]",
            "name": f"{slot_a}RowSpecA",
            "module": f"ArithS.Tau.Rows.{tmpl_a[len('Tau'):]}",
            "bits": bits,
        })

    hashed = [json.dumps(r, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
              for r in rows + floor_bits]
    return {
        "schema_version": 1,
        "system": "sprime",
        "source_digest": str(_fnv1a64("".join(hashed))),
        "order": list(PAPER_ORDER),
        "rows": rows,
        "floor_bits": floor_bits,
    }


def main() -> None:
    full = build()
    OUT.write_text(json.dumps(full, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    n_bits = sum(len(r["bits"]) for r in full["rows"])
    print(f"wrote {OUT}: {len(full['rows'])} rows, {n_bits} row slots, "
          f"{len(full['floor_bits'])} floor bits (from {base_export()})")
    partial = build(templates=PARTIAL_TEMPLATES)
    OUT_PARTIAL.write_text(json.dumps(partial, indent=1, ensure_ascii=False) + "\n",
                           encoding="utf-8")
    print(f"wrote {OUT_PARTIAL}: {len(partial['rows'])} rows, "
          f"{sum(len(r['bits']) for r in partial['rows'])} row slots, "
          f"{len(partial['floor_bits'])} floor bits")


if __name__ == "__main__":
    main()

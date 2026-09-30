"""Build `sprime_outcome_theorems.sample.json` — a stand-in for the Lean export.

The real file, `app/generated/sprime_outcome_theorems.json`, is written by
`lake exe export_sprime_outcomes` from the `@[outcomeA]`/`@[floorA]` theorems in
`arith/ArithS/Outcome/` (`SPRIME_SOURCE_OF_TRUTH.md` §1.1–1.2). Until that exporter has
run at least once the test-suite needs a document in the same schema, so this script
derives one from the cell ledger `ROUTE_B_CENSUS.md`, which is script-exact over the
155 engine cells:

* a row with an `S'` value is a THEOREM (`provenance: "sprime"`);
* a `GENUINE-FLOOR` row is a FLOOR whose `pair` is the ENGINE value (the `¬A_k` half
  of `dich_<L>_vs_<R>`), with a placeholder `hinge` text — the real export
  pretty-prints the inline `□[k] φ` hinge;
* `EXCLUDED` rows (LegibleBot, OptimBot, WaryBot's floor cells) are skipped.

Names lose the `llm_` prefix (`S'` has one namespace); regime `eventual`, `fuel_pad 0`,
`staggered false` for every row; `left`/`right` read `X k` for budgeted bots and `X`
for the closed ones. The digest is computed with the same FNV-1a the loader verifies.

Run (from `app/`): `uv run python tests/fixtures/make_sprime_fixture.py`
and commit the regenerated sample.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[2]
LEDGER = (WORKSPACE / "engine" / "PrisonersDilemma" / "Research" / "Notes"
          / "ROUTE_B_CENSUS.md")
OUT = HERE / "sprime_outcome_theorems.sample.json"

# Bots whose engine definition takes no budget (`CooperateBot`, not `CooperateBot k`).
CLOSED_BOTS = {"CooperateBot", "DefectBot", "DBot", "EBot", "OBot", "TitForTatBot", "MirrorBot"}

_ROW = re.compile(r"^\|\s*(?P<name>(?:llm_)?outcome_\w+)\s*\|\s*(?P<engine>[^|]+?)\s*\|"
                  r"\s*(?P<sprime>[^|]+?)\s*\|\s*(?P<cls>[^|]+?)\s*\|")


def _pair(text: str) -> list[str] | None:
    text = text.strip()
    if text == "none":
        return None
    m = re.fullmatch(r"\((C|D),\s*(C|D)\)", text)
    if m is None:
        raise ValueError(f"unreadable cell value {text!r}")
    return [m.group(1), m.group(2)]


def _bot_text(bot: str) -> str:
    return bot if bot in CLOSED_BOTS else f"{bot} k"


def build(ledger: Path = LEDGER) -> dict:
    sys.path.insert(0, str(WORKSPACE / "app" / "src"))
    from pd_runner.eval.outcome_matrix import _fnv1a64

    theorems: list[dict] = []
    floors: list[dict] = []
    for line in ledger.read_text(encoding="utf-8").splitlines():
        m = _ROW.match(line)
        if m is None:
            continue
        cls = m.group("cls").strip()
        name = m.group("name")
        core = name[len("llm_"):] if name.startswith("llm_") else name
        left, right = core[len("outcome_"):].split("_vs_")
        base = {
            "name": core,
            "module": f"ArithS.Outcome.Matrix.{left}",
            "file": f"{left}.lean",
            "left_bot": left,
            "right_bot": right,
            "budget_regime": "eventual",
            "fuel_pad": 0,
            "staggered": False,
            "left": _bot_text(left),
            "right": _bot_text(right),
        }
        if cls.startswith("EXCLUDED"):
            continue
        if cls.startswith("GENUINE-FLOOR"):
            floors.append({
                **base,
                "module": "ArithS.Outcome.Floors",
                "file": "Floors.lean",
                "name": f"{core}_floor",
                "pair": _pair(m.group("engine")),
                "provenance": "floor_dichotomy",
                "hinge": f"LenBox TAct k (guard of {left})",
                "dichotomy": f"dich_{left}_vs_{right}",
            })
            continue
        sprime = m.group("sprime").strip()
        if sprime == "—":
            raise ValueError(f"{name}: class {cls!r} but no S' value")
        theorems.append({**base, "pair": _pair(sprime), "provenance": "sprime"})

    theorems.sort(key=lambda t: t["name"])
    floors.sort(key=lambda t: t["name"])
    companions: list[dict] = []
    rows = [json.dumps(t, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            for t in theorems + companions + floors]
    return {
        "schema_version": 1,
        "system": "sprime",
        "source_digest": str(_fnv1a64("".join(rows))),
        "theorems": theorems,
        "companions": companions,
        "floors": floors,
    }


def main() -> None:
    doc = build()
    OUT.write_text(json.dumps(doc, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {OUT}: {len(doc['theorems'])} theorems, {len(doc['floors'])} floors")


if __name__ == "__main__":
    main()

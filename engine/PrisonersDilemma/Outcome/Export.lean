import PrisonersDilemma.Outcome.Lint
import Lean

/-!
# JSON export of the outcome matrix

`lake exe export_outcomes [out.json]` writes the `@[outcome]`-tagged cells as structured
data, replacing the regex scraping in `app/src/pd_runner/eval/outcome_matrix.py`. The
artifact is COMMITTED so the Python side (tests, the FastAPI service) works without a Lean
toolchain; `source_digest` lets the linter detect a stale or hand-edited file.

`PD.outcome` is `noncomputable`, but nothing here evaluates it — the exported data is
names, regimes and literals recovered by `Expr` inspection.
-/

open Lean

namespace PD.Outcome

/-- Order-insensitive-ish digest over the exported rows. Cheap, and enough to catch a
    stale or hand-edited JSON. -/
def digestOf (rows : Array String) : UInt64 :=
  rows.foldl (init := 1469598103934665603) fun h s =>
    s.foldl (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211) h

def cellJson (c : CellInfo) : Json :=
  Json.mkObj [
    ("name",          Json.str (shortName c.name).toString),
    ("module",        Json.str c.module.toString),
    -- The source basename, for parity with the legacy scanner's `file` field.
    ("file",          Json.str ((c.module.toString.splitOn ".").getLast!  ++ ".lean")),
    ("left_bot",      Json.str c.leftBot.toString),
    ("right_bot",     Json.str c.rightBot.toString),
    ("budget_regime", Json.str c.regime.toString),
    ("fuel_pad",      Json.num c.pad),
    ("pair", match c.pair with
      | none => Json.null
      | some (a, b) => Json.arr #[Json.str a.toString, Json.str b.toString]),
    ("side_conditions", Json.arr (c.sideConds.map Json.str)),
    ("staggered",     Json.bool c.staggered)
  ]

/-- Build the whole document (sorted by name, so the output is deterministic). -/
def buildJson (cells : Array CellInfo) : Json :=
  let sorted := cells.qsort fun a b =>
    (shortName a.name).toString < (shortName b.name).toString
  let rows := sorted.map cellJson
  let digest := digestOf (rows.map fun r => r.compress)
  Json.mkObj [
    ("schema_version", Json.num 1),
    ("source_digest",  Json.str (toString digest)),
    ("theorems",       Json.arr rows)
  ]

end PD.Outcome

open Lean PD.Outcome in
/-- Entry point for `lake exe export_outcomes`. Imports the built library, inspects every
    tagged declaration and writes the JSON. -/
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath :=
    args.head?.getD "../app/generated/outcome_theorems.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `PrisonersDilemma }] {}
  let tagged := taggedOutcomes env
  let act : MetaM (Array CellInfo) := do
    let mut acc : Array CellInfo := #[]
    for n in tagged do
      acc := acc.push (← inspectCell env n)
    return acc
  let (cells, _) ← (act.run').toIO
    { fileName := "<export>", fileMap := default } { env }
  let doc := buildJson cells
  IO.FS.writeFile out (doc.pretty ++ "\n")
  IO.println s!"wrote {cells.size} outcome cells to {out}"
  return 0

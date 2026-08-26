import PrisonersDilemma.Outcome.Lint
import PrisonersDilemma.Tau.Lint
import Lean

/-!
# JSON export of the outcome matrix

`lake exe export_outcomes [out.json] [tau_rows.json]` writes the `@[outcome]`-tagged cells
(and the `@[tau_row]` bit rows, `Tau/RowSpec.lean`) as structured data, replacing the regex scraping in `app/src/pd_runner/eval/outcome_matrix.py`. The
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

/-- One tau row: the template, its order, and its bits keyed by slot. -/
def rowJson (r : PD.Tau.RowInfo) : Json :=
  Json.mkObj [
    ("name",     Json.str (shortName r.name).toString),
    ("module",   Json.str r.module.toString),
    ("template", Json.str r.template.toString),
    ("order",    Json.str r.order.toString),
    ("bits",     Json.mkObj (r.bits.toList.map fun (s, a) => (s.toString, Json.str a.toString)))
  ]

def buildTauJson (rows : Array PD.Tau.RowInfo) (order : Array Name) : Json :=
  let sorted := rows.qsort fun a b => a.template.toString < b.template.toString
  let rs := sorted.map rowJson
  Json.mkObj [
    ("schema_version", Json.num 1),
    ("source_digest",  Json.str (toString (digestOf (rs.map fun r => r.compress)))),
    ("order",          Json.arr (order.map fun n => Json.str (shortName n).toString)),
    ("rows",           Json.arr rs)
  ]

end PD.Outcome

open Lean PD.Outcome in
/-- Entry point for `lake exe export_outcomes`. Imports the built library, inspects every
    tagged declaration and writes the JSON. -/
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath :=
    args.head?.getD "../app/generated/outcome_theorems.json"
  let tauOut : System.FilePath := match args with
    | _ :: t :: _ => t
    | _           => "../app/generated/tau_rows.json"
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
  let tauAct : MetaM (Array PD.Tau.RowInfo × Array Name) := do
    let rows ← PD.Tau.inspectAllRows env
    let order ← PD.Tau.listCtors (mkConst ``PD.Tau.tauOrder)
    return (rows, order)
  let ((rows, order), _) ← (tauAct.run').toIO
    { fileName := "<export>", fileMap := default } { env }
  IO.FS.writeFile tauOut ((buildTauJson rows order).pretty ++ "\n")
  IO.println s!"wrote {rows.size} tau rows to {tauOut}"
  return 0

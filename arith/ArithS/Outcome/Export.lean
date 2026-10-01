import ArithS.Outcome.Check
import ArithS.Tau.Check
import Lean

/-!
# ArithS.Outcome.Export — JSON export of the PA-`S'` matrix

`lake exe export_sprime_outcomes [out.json] [tau_out.json]` writes the `@[outcomeA]` cells and the `@[floorA]` floors to
`app/generated/sprime_outcome_theorems.json` (default path `../app/generated/sprime_outcome_theorems.json`,
relative to `arith/`), and the `@[tau_rowA]` rows and `@[tau_floor_bitA]` floor bits (`Tau/Spec.lean`, Phase 3) to
`app/generated/sprime_tau_rows.json` (second argument; see `buildTauJsonA` for the schema). The schema is the engine's (`PrisonersDilemma/Outcome/Export.lean`), so the Python loader
is shared, plus `system`, a `provenance` per row and the `floors` array
(`Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §1.2):

    { "schema_version": 1, "system": "sprime", "source_digest": "<fnv1a64>",
      "theorems":   [ { name, module, file, left_bot, right_bot, budget_regime, fuel_pad: 0, pair, staggered,
                        left, right, provenance: "sprime" } ],
      "companions": [],
      "floors":     [ { …the same fields…, provenance: "floor_dichotomy", pair: <the engine-side value>,
                        hinge: "<the hinge, □[k] notation>", dichotomy: "dich_<L>_vs_<R>" } ] }

`source_digest` is the engine's `digestOf` — FNV-1a (64-bit, over Unicode code points) folded over the
`Json.compress` of every row — over `theorems ++ companions ++ floors` in that order, each sorted by name. The
Python side recomputes it as `json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False)` per row
(the hinge text is not ASCII). `fuel_pad` is `0` on every `S'` row (fuel is existential in `OutcomeSpecA`);
floors are always `eventual`.

The exporter imports `ArithS.Outcome.Check` and `ArithS.Tau.Check` (not the whole `ArithS`), so what it writes has
passed both censuses.

**The tau file** (`app/generated/sprime_tau_rows.json`) is the engine's `tau_rows.json` schema plus the floor bits:

    { "schema_version": 1, "system": "sprime", "source_digest": "<fnv1a64 over rows ++ floor_bits>",
      "order": [ the 14 names of `paperOrder` ],
      "rows":  [ { name, module, template, order: "[coop, defect, …]" (the row's OWN literal order, a string),
                   bits: { slot: "C" | "D" } } ],
      "floor_bits": [ { name, module, template, slot, action, hinge, dichotomy } ] }

`order` on a row is the row's literal slot list (the engine prints the NAME `tauOrder`; an `S'` row states only its
theorem slots, its floor slots being separate theorems), and `dichotomy` is the base `dich_<L>_vs_<R>` the floor bit
is one bit of (`Tau/Lint.expectedFloorBits`). The digest is the same recipe, over the row objects then the floor-bit
objects, each array sorted by name.
-/

open Lean

namespace ArithS.Outcome

/-- The engine's digest: FNV-1a over the concatenated rows, character by character. -/
def digestOf (rows : Array String) : UInt64 :=
  rows.foldl (init := 1469598103934665603) fun h s =>
    s.foldl (fun h c => (h ^^^ c.toNat.toUInt64) * 1099511628211) h

private def baseFields (c : CellInfo) : List (String × Json) := [
  ("name",          Json.str (shortName c.name).toString),
  ("module",        Json.str c.module.toString),
  ("file",          Json.str ((c.module.toString.splitOn ".").getLast! ++ ".lean")),
  ("left_bot",      Json.str c.leftBot.toString),
  ("right_bot",     Json.str c.rightBot.toString),
  ("budget_regime", Json.str c.regime.toString),
  ("fuel_pad",      Json.num c.pad),
  ("pair", match c.pair with
    | none => Json.null
    | some (a, b) => Json.arr #[Json.str a.toString, Json.str b.toString]),
  ("staggered",     Json.bool c.staggered),
  ("left",          Json.str c.leftText),
  ("right",         Json.str c.rightText)
]

/-- A cell row: the engine's fields plus `provenance: "sprime"`. -/
def cellJson (c : CellInfo) : Json :=
  Json.mkObj (baseFields c ++ [("provenance", Json.str "sprime")])

/-- A floor row: the engine's fields plus `provenance: "floor_dichotomy"`, the hinge and the dichotomy. -/
def floorJson (c : CellInfo) : Json :=
  Json.mkObj (baseFields c ++ [
    ("provenance", Json.str "floor_dichotomy"),
    ("hinge",      Json.str c.hinge),
    ("dichotomy",  Json.str c.dichotomy.toString)
  ])

/-- The whole document, every array sorted by name; the digest covers cells, companions and floors. -/
def buildJson (cells floors : Array CellInfo) : Json :=
  let sort := fun (xs : Array CellInfo) => xs.qsort fun a b =>
    (shortName a.name).toString < (shortName b.name).toString
  let rows := (sort cells).map cellJson
  let crows : Array Json := #[]
  let frows := (sort floors).map floorJson
  let digest := digestOf ((rows ++ crows ++ frows).map fun r => r.compress)
  Json.mkObj [
    ("schema_version", Json.num 1),
    ("system",         Json.str "sprime"),
    ("source_digest",  Json.str (toString digest)),
    ("theorems",       Json.arr rows),
    ("companions",     Json.arr crows),
    ("floors",         Json.arr frows)
  ]

/-! ### The tau rows -/

/-- One tau row: the template, its own literal order, and its bits keyed by slot. -/
def rowJsonA (r : ArithS.Tau.RowInfoA) : Json :=
  Json.mkObj [
    ("name",     Json.str (shortName r.name).toString),
    ("module",   Json.str r.module.toString),
    ("template", Json.str r.template.toString),
    ("order",    Json.str r.order),
    ("bits",     Json.mkObj (r.bits.toList.map fun (s, a) => (s.toString, Json.str a.toString)))
  ]

/-- One floor bit: the cell, its engine-side action, the hinge text and the base dichotomy. -/
def floorBitJson (f : ArithS.Tau.FloorBitInfoA) : Json :=
  Json.mkObj [
    ("name",      Json.str (shortName f.name).toString),
    ("module",    Json.str f.module.toString),
    ("template",  Json.str f.template.toString),
    ("slot",      Json.str f.slot.toString),
    ("action",    Json.str f.action.toString),
    ("hinge",     Json.str f.hinge),
    ("dichotomy", Json.str f.dichotomy)
  ]

/-- The tau document; the digest covers the rows then the floor bits, both sorted by name. -/
def buildTauJsonA (rows : Array ArithS.Tau.RowInfoA) (floors : Array ArithS.Tau.FloorBitInfoA) (order : Array Name) : Json :=
  let rs := (rows.qsort fun a b => (shortName a.name).toString < (shortName b.name).toString).map rowJsonA
  let fs := (floors.qsort fun a b => (shortName a.name).toString < (shortName b.name).toString).map floorBitJson
  Json.mkObj [
    ("schema_version", Json.num 1),
    ("system",         Json.str "sprime"),
    ("source_digest",  Json.str (toString (digestOf ((rs ++ fs).map fun r => r.compress)))),
    ("order",          Json.arr (order.map fun n => Json.str n.toString)),
    ("rows",           Json.arr rs),
    ("floor_bits",     Json.arr fs)
  ]

end ArithS.Outcome

open Lean ArithS.Outcome in
/-- Entry point for `lake exe export_sprime_outcomes`. Imports the built check module, inspects every tagged
    declaration and writes the JSON. -/
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath :=
    args.head?.getD "../app/generated/sprime_outcome_theorems.json"
  let tauOut : System.FilePath := match args with
    | _ :: t :: _ => t
    | _           => "../app/generated/sprime_tau_rows.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ArithS.Outcome.Check }, { module := `ArithS.Tau.Check }] {}
  let act : MetaM (Array CellInfo × Array CellInfo) := do
    let mut cells : Array CellInfo := #[]
    for n in taggedOutcomesA env do
      cells := cells.push (← inspectCellA env n)
    let mut floors : Array CellInfo := #[]
    for n in taggedFloorsA env do
      floors := floors.push (← inspectFloorA env n)
    return (cells, floors)
  let ((cells, floors), _) ← (act.run').toIO
    { fileName := "<export>", fileMap := default } { env }
  let doc := buildJson cells floors
  IO.FS.writeFile out (doc.pretty ++ "\n")
  IO.println s!"wrote {cells.size} S' outcome cells and {floors.size} floors to {out}"
  let tauAct : MetaM (Array ArithS.Tau.RowInfoA × Array ArithS.Tau.FloorBitInfoA × Array Name) := do
    let rows ← ArithS.Tau.inspectAllRowsA env
    let fbs ← ArithS.Tau.inspectAllFloorBitsA env
    let order ← ArithS.Tau.paperOrderNames
    return (rows, fbs, order)
  let ((rows, fbs, order), _) ← (tauAct.run').toIO
    { fileName := "<export>", fileMap := default } { env }
  IO.FS.writeFile tauOut ((buildTauJsonA rows fbs order).pretty ++ "\n")
  IO.println s!"wrote {rows.size} S' tau rows and {fbs.size} floor bits to {tauOut}"
  return 0

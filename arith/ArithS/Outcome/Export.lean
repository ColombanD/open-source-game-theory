import ArithS.Outcome.Check
import Lean

/-!
# ArithS.Outcome.Export — JSON export of the PA-`S'` matrix

`lake exe export_sprime_outcomes [out.json]` writes the `@[outcomeA]` cells and the `@[floorA]` floors to
`app/generated/sprime_outcome_theorems.json` (default path `../app/generated/sprime_outcome_theorems.json`,
relative to `arith/`). The schema is the engine's (`PrisonersDilemma/Outcome/Export.lean`), so the Python loader
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

The exporter imports `ArithS.Outcome.Check` (not the whole `ArithS`), so what it writes has passed the census.
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

end ArithS.Outcome

open Lean ArithS.Outcome in
/-- Entry point for `lake exe export_sprime_outcomes`. Imports the built check module, inspects every tagged
    declaration and writes the JSON. -/
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath :=
    args.head?.getD "../app/generated/sprime_outcome_theorems.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ArithS.Outcome.Check }] {}
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
  return 0

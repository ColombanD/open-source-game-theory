import ArithS.Tau.Spec
import ArithS.Tau.Attr
import ArithS.Outcome.Lint
import Lean

/-!
# ArithS.Tau.Lint — the PA-`S'` tau row linter and census (Phase 3)

The engine's `Tau/Lint.lean` adapted to `RowSpecA`/`FloorBitA` (`Tau/Spec.lean`), with the hinge printer of
`Outcome/Lint.lean`. Every failure is a `throwError`, so `lake build` (target `ArithSTauCheck`) rejects a bad row.

* `inspectRowA` — a `@[tau_rowA]` theorem is an unconditional `ArithS.Tau.RowSpecA <template> <order> <row>`
  (head matched SYNTACTICALLY): the template a literal `Tmpl` constructor of `paperOrder`, the order a literal
  `List Tmpl` whose constructors form an order-preserving SUBLIST of `paperOrder`, the row evaluating by `whnf` to
  `C`/`D` at every slot, the name `<t>RowSpecA`.
* `inspectFloorBitA` — a `@[tau_floor_bitA]` theorem is `ArithS.Tau.FloorBitA .<t> .<T> (fun k ↦ …) a`, both
  templates literal members of `paperOrder`, the hinge an inline lambda (printed by `hingeText`), the action a
  literal, the name `<t>RowSpecA_<T>_floor`; its `(template, slot)` must be one of the 47 `‡` cells of the table
  in `SPRIME_SOURCE_OF_TRUTH.md` §3 (`expectedFloorBits`, hard-coded with the engine-side action and the base
  dichotomy), with that action.
* `#check_tau_rowsA` — the census over `paperOrder²` (196 bits): every bit is covered by at most one row slot and
  at most one floor bit, never both; a row slot on a `‡` cell is an error ("a floor became a theorem — update the
  table"), a floor bit off the `‡` list is an error ("a theorem became a floor"); a template has at most one row.
  **Partial roster during Phase 3**: the plain command logs the UNCOVERED bits and the missing templates as
  `info` and succeeds (the build stays green while the rows land one by one); `#check_tau_rowsA strict` makes
  every gap an error — the form to switch to when the 14 rows and 47 floor bits are all in (five bits stay
  UNSTATED under the present coding — the budget-snapshot obstruction, §3 of the design note — so the plain form
  stays until that decision).
-/

open Lean Elab Command Meta

namespace ArithS.Tau

/-- Metadata of one validated row. -/
structure RowInfoA where
  name     : Name
  module   : Name
  template : Name
  /-- The row's own literal order, printed `[coop, defect, …]`. -/
  order    : String
  /-- The slots, in the row's order. -/
  slots    : Array Name
  /-- `(slot, action)` in order, actions `C`/`D`. -/
  bits     : Array (Name × Name)
  deriving Repr

/-- Metadata of one validated floor bit. -/
structure FloorBitInfoA where
  name      : Name
  module    : Name
  template  : Name
  slot      : Name
  action    : Name
  /-- The hinge, printed with the binder named `k` (`Outcome/Lint.hingeText`). -/
  hinge     : String
  /-- The base dichotomy the bit is the engine-side half of (from `expectedFloorBits`). -/
  dichotomy : String
  deriving Repr

/-- One expected floor bit: the `‡` cells of the table (`SPRIME_SOURCE_OF_TRUTH.md` §3), with the ENGINE-SIDE
action and the base dichotomy (`Cells/FloorDichotomy.lean`) it is the bit of. The field is carried into the export
and never resolved to a constant: for the six tau images of the RED CELL (`dupoc/maxconfidence/minconfidence ×
cupod` and back), which are floors in `S'` although the base cell is a THEOREM (`Tau/Entangled/DupocCupod.lean`), it
names that base theorem, `outcome_DupocBot_vs_CupodBot`, since no `dich_` exists. -/
structure ExpectedFloor where
  template  : Name
  slot      : Name
  action    : Name
  dichotomy : String
  deriving Repr

private def ef (t s a : String) (d : String) : ExpectedFloor :=
  ⟨Name.mkSimple t, Name.mkSimple s, Name.mkSimple a, d⟩

/-- **The 47 `‡` cells** of the Phase-3 table, row by row (engine-side action; base dichotomy). A floor that
becomes a theorem, or a theorem that becomes a floor, fails the census and forces the table — and this list —
to be updated together. 2026-10-01 (Phase 3c/3d): the six tau images of the red cell joined the list — theorems
in the base (`outcome_DupocBot_vs_CupodBot`, by τ-symmetry), FLOORS on the compiled `.sys` systems (no τ-symmetry
inside one system; `Tau/Entangled/DupocCupod.lean`). -/
def expectedFloorBits : Array ExpectedFloor := #[
  -- dupoc: ebot D‡, dbot D‡, cupodTroll D‡, cupod D‡ (red cell), prudent D‡
  ef "dupoc" "ebot" "D" "dich_DupocBot_vs_EBot",
  ef "dupoc" "dbot" "D" "dich_DupocBot_vs_DBot",
  ef "dupoc" "cupodTroll" "D" "dich_DupocBot_vs_CupodTrollBot",
  ef "dupoc" "cupod" "D" "outcome_DupocBot_vs_CupodBot",
  ef "dupoc" "prudent" "D" "dich_PrudentBot_vs_DupocBot",
  -- ebot: dupoc C‡, cimcic C‡, prudent C‡, maxconf C‡, minconf C‡
  ef "ebot" "dupoc" "C" "dich_DupocBot_vs_EBot",
  ef "ebot" "cimcic" "C" "dich_CIMCIC_vs_EBot",
  ef "ebot" "prudent" "C" "dich_PrudentBot_vs_EBot",
  ef "ebot" "maxconfidence" "C" "dich_DupocBot_vs_EBot",
  ef "ebot" "minconfidence" "C" "dich_DupocBot_vs_EBot",
  -- obot: cupod D‡
  ef "obot" "cupod" "D" "dich_CupodBot_vs_OBot",
  -- dbot: dupoc C‡, cimcic C‡, maxconf C‡, minconf C‡
  ef "dbot" "dupoc" "C" "dich_DupocBot_vs_DBot",
  ef "dbot" "cimcic" "C" "dich_CIMCIC_vs_DBot",
  ef "dbot" "maxconfidence" "C" "dich_DupocBot_vs_DBot",
  ef "dbot" "minconfidence" "C" "dich_DupocBot_vs_DBot",
  -- cupodTroll: dupoc C‡, cimcic C‡, maxconf C‡, minconf C‡
  ef "cupodTroll" "dupoc" "C" "dich_DupocBot_vs_CupodTrollBot",
  ef "cupodTroll" "cimcic" "C" "dich_CIMCIC_vs_CupodTrollBot",
  ef "cupodTroll" "maxconfidence" "C" "dich_DupocBot_vs_CupodTrollBot",
  ef "cupodTroll" "minconfidence" "C" "dich_DupocBot_vs_CupodTrollBot",
  -- cupod: dupoc C‡ (red cell), obot C‡, cimcic C‡, prudent C‡, maxconf C‡ (red cell), minconf C‡ (red cell)
  ef "cupod" "dupoc" "C" "outcome_DupocBot_vs_CupodBot",
  ef "cupod" "obot" "C" "dich_CupodBot_vs_OBot",
  ef "cupod" "cimcic" "C" "dich_CIMCIC_vs_CupodBot",
  ef "cupod" "prudent" "C" "dich_CupodBot_vs_PrudentBot",
  ef "cupod" "maxconfidence" "C" "outcome_DupocBot_vs_CupodBot",
  ef "cupod" "minconfidence" "C" "outcome_DupocBot_vs_CupodBot",
  -- cimcic: ebot D‡, dbot D‡, cupodTroll D‡, cupod D‡, prudent D‡
  ef "cimcic" "ebot" "D" "dich_CIMCIC_vs_EBot",
  ef "cimcic" "dbot" "D" "dich_CIMCIC_vs_DBot",
  ef "cimcic" "cupodTroll" "D" "dich_CIMCIC_vs_CupodTrollBot",
  ef "cimcic" "cupod" "D" "dich_CIMCIC_vs_CupodBot",
  ef "cimcic" "prudent" "D" "dich_CIMCIC_vs_PrudentBot",
  -- prudent: dupoc D‡, ebot D‡, cupod D‡, cimcic D‡, prudent D‡, maxconf D‡, minconf D‡
  ef "prudent" "dupoc" "D" "dich_PrudentBot_vs_DupocBot",
  ef "prudent" "ebot" "D" "dich_PrudentBot_vs_EBot",
  ef "prudent" "cupod" "D" "dich_PrudentBot_vs_CupodBot",
  ef "prudent" "cimcic" "D" "dich_CIMCIC_vs_PrudentBot",
  ef "prudent" "prudent" "D" "dich_PrudentBot_vs_PrudentBot",
  ef "prudent" "maxconfidence" "D" "dich_PrudentBot_vs_DupocBot",
  ef "prudent" "minconfidence" "D" "dich_PrudentBot_vs_DupocBot",
  -- maxconf: ebot D‡, dbot D‡, cupodTroll D‡, cupod D‡ (red cell), prudent D‡
  ef "maxconfidence" "ebot" "D" "dich_DupocBot_vs_EBot",
  ef "maxconfidence" "dbot" "D" "dich_DupocBot_vs_DBot",
  ef "maxconfidence" "cupodTroll" "D" "dich_DupocBot_vs_CupodTrollBot",
  ef "maxconfidence" "cupod" "D" "outcome_DupocBot_vs_CupodBot",
  ef "maxconfidence" "prudent" "D" "dich_PrudentBot_vs_DupocBot",
  -- minconf: ebot D‡, dbot D‡, cupodTroll D‡, cupod D‡ (red cell), prudent D‡
  ef "minconfidence" "ebot" "D" "dich_DupocBot_vs_EBot",
  ef "minconfidence" "dbot" "D" "dich_DupocBot_vs_DBot",
  ef "minconfidence" "cupodTroll" "D" "dich_DupocBot_vs_CupodTrollBot",
  ef "minconfidence" "cupod" "D" "outcome_DupocBot_vs_CupodBot",
  ef "minconfidence" "prudent" "D" "dich_PrudentBot_vs_DupocBot"
]

/-- `whnf` a closed `List Tmpl` term down to its constructor names (the engine's `listCtors`). -/
partial def listCtors (e : Expr) : MetaM (Array Name) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, #[_, h, t]) =>
    let some c := (← whnf h).constName?
      | throwError "tau row: order entry is not a constructor: {← ppExpr h}"
    return #[c] ++ (← listCtors t)
  | _ => throwError "tau row: order is not a list literal: {← ppExpr e}"

/-- The 14 paper templates, as short names, in order. -/
def paperOrderNames : MetaM (Array Name) := do
  return (← listCtors (mkConst ``ArithS.Tau.paperOrder)).map ArithS.Outcome.shortName

/-- `xs` is an order-preserving subsequence of `ys`. -/
def isSublistOf (xs ys : Array Name) : Bool := Id.run do
  let mut j := 0
  for x in xs do
    while j < ys.size && ys.getD j .anonymous != x do j := j + 1
    if j ≥ ys.size then return false
    j := j + 1
  return true

/-- A row's order, printed `[coop, defect, …]`. -/
def orderText (slots : Array Name) : String :=
  "[" ++ ", ".intercalate (slots.toList.map (·.toString)) ++ "]"

private def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames.getD idx.toNat .anonymous
  | none     => Name.anonymous

/-- A literal `Tmpl` constructor, as its short name, or throw. -/
private def tmplOf (tag : String) (n : Name) (what : String) (e : Expr) : MetaM Name := do
  let some c := (← whnf e).constName?
    | throwError "@[{tag}] {n}: the {what} must be a literal `Tmpl` constructor, got `{← ppExpr e}`"
  return ArithS.Outcome.shortName c

/-- Validate one `@[tau_rowA]` theorem, returning its bits. -/
def inspectRowA (env : Environment) (n : Name) : MetaM RowInfoA := do
  let some ci := env.find? n
    | throwError "@[tau_rowA] {n}: not found in the environment"
  let ty := ci.type
  if ty.isForall then
    throwError "@[tau_rowA] {n}: a row takes no hypotheses — `RowSpecA` quantifies the budget itself \
      (`∃ k₂, ∀ k > k₂, …`); a floor slot is its own `@[tau_floor_bitA]` theorem"
  let (fn, args) := (ty.getAppFn, ty.getAppArgs)
  unless fn.isConstOf ``ArithS.Tau.RowSpecA do
    throwError "@[tau_rowA] {n} is OFF-TEMPLATE: its statement must be \
      `ArithS.Tau.RowSpecA <template> <order> <row>`, got\n  {← ppExpr ty}"
  unless args.size == 3 do
    throwError "@[tau_rowA] {n}: expects 3 arguments, got {args.size}"
  let paper ← paperOrderNames
  let tmpl ← tmplOf "tau_rowA" n "template" (args.getD 0 default)
  unless paper.contains tmpl do
    throwError "@[tau_rowA] {n}: the template `{tmpl}` is not one of the 14 paper templates (`paperOrder`)"
  -- the order: a LITERAL list (not a named constant), a sublist of `paperOrder`
  unless (args.getD 1 default).getAppFn.isConstOf ``List.cons || (args.getD 1 default).getAppFn.isConstOf ``List.nil do
    throwError "@[tau_rowA] {n}: the order must be a literal `List Tmpl` (write the slots out), got `{← ppExpr (args.getD 1 default)}`"
  let slots := (← listCtors (args.getD 1 default)).map ArithS.Outcome.shortName
  unless isSublistOf slots paper do
    throwError "@[tau_rowA] {n}: the order {orderText slots} is not an order-preserving sublist of `paperOrder` \
      {orderText paper}"
  let mut bits : Array (Name × Name) := #[]
  for s in slots do
    let v ← whnf (mkApp (args.getD 2 default) (mkConst (`PD.Tau.Tmpl ++ s)))
    match v.constName? with
    | some c =>
      unless c == ``PD.Action.C || c == ``PD.Action.D do
        throwError "@[tau_rowA] {n}: row at {s} is not a literal action: {← ppExpr v}"
      bits := bits.push (s, ArithS.Outcome.shortName c)
    | none => throwError "@[tau_rowA] {n}: row at {s} does not evaluate to an action: {← ppExpr v}"
  let expected := tmpl.toString ++ "RowSpecA"
  unless (ArithS.Outcome.shortName n).toString == expected do
    throwError "@[tau_rowA] {n}: NAME/STATEMENT MISMATCH — the statement is about `{tmpl}`, so the theorem must \
      be named `{expected}`"
  return { name := n, module := moduleOf env n, template := tmpl, order := orderText slots, slots := slots, bits := bits }

/-- Validate one `@[tau_floor_bitA]` theorem. -/
def inspectFloorBitA (env : Environment) (n : Name) : MetaM FloorBitInfoA := do
  let some ci := env.find? n
    | throwError "@[tau_floor_bitA] {n}: not found in the environment"
  let ty := ci.type
  if ty.isForall then
    throwError "@[tau_floor_bitA] {n}: a floor bit takes no hypotheses — the hinge is written inline"
  let (fn, args) := (ty.getAppFn, ty.getAppArgs)
  unless fn.isConstOf ``ArithS.Tau.FloorBitA do
    throwError "@[tau_floor_bitA] {n} is OFF-TEMPLATE: its statement must be \
      `ArithS.Tau.FloorBitA <template> <slot> (fun k ↦ …) <action>`, got\n  {← ppExpr ty}"
  unless args.size == 4 do
    throwError "@[tau_floor_bitA] {n}: expects 4 arguments, got {args.size}"
  let paper ← paperOrderNames
  let tmpl ← tmplOf "tau_floor_bitA" n "template" (args.getD 0 default)
  let slot ← tmplOf "tau_floor_bitA" n "slot" (args.getD 1 default)
  unless paper.contains tmpl && paper.contains slot do
    throwError "@[tau_floor_bitA] {n}: `{tmpl} × {slot}` is not a cell of the paper table (`paperOrder²`)"
  let hinge ← match args.getD 2 default with
    | .lam _ _ b _ => ArithS.Outcome.hingeText (b.instantiate1 (mkFVar ⟨`k⟩))
    | h => throwError "@[tau_floor_bitA] {n}: the hinge must be an inline lambda `fun k ↦ …`, got `{← ppExpr h}`"
  let some act := (← whnf (args.getD 3 default)).constName?
    | throwError "@[tau_floor_bitA] {n}: the action must be a literal `C`/`D`"
  unless act == ``PD.Action.C || act == ``PD.Action.D do
    throwError "@[tau_floor_bitA] {n}: the action must be a literal `C`/`D`, got `{act}`"
  let action := ArithS.Outcome.shortName act
  let expected := s!"{tmpl}RowSpecA_{slot}_floor"
  unless (ArithS.Outcome.shortName n).toString == expected do
    throwError "@[tau_floor_bitA] {n}: NAME/STATEMENT MISMATCH — the statement is the bit `{tmpl} × {slot}`, so \
      the theorem must be named `{expected}`"
  let some e := expectedFloorBits.find? fun e => e.template == tmpl && e.slot == slot
    | throwError "@[tau_floor_bitA] {n}: `{tmpl} × {slot}` is NOT a `‡` cell of the Phase-3 table — a theorem that \
      became a floor; state it as a row slot, or update the table in `SPRIME_SOURCE_OF_TRUTH.md` §3 AND \
      `expectedFloorBits` together"
  unless e.action == action do
    throwError "@[tau_floor_bitA] {n}: the table's engine-side value at `{tmpl} × {slot}` is `{e.action}`, the \
      theorem states `{action}`"
  return { name := n, module := moduleOf env n, template := tmpl, slot := slot, action := action, hinge := hinge
           dichotomy := e.dichotomy }

def inspectAllRowsA (env : Environment) : MetaM (Array RowInfoA) := do
  let mut acc := #[]
  for n in taggedTauRowsA env do
    acc := acc.push (← inspectRowA env n)
  return acc

def inspectAllFloorBitsA (env : Environment) : MetaM (Array FloorBitInfoA) := do
  let mut acc := #[]
  for n in taggedTauFloorBitsA env do
    acc := acc.push (← inspectFloorBitA env n)
  return acc

/-- The census (see the module docstring); `strict` turns the coverage gaps into errors. -/
def runCensus (strict : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let (rows, floors, paper) ← liftTermElabM do
    pure (← inspectAllRowsA env, ← inspectAllFloorBitsA env, ← paperOrderNames)
  -- one row per template
  let mut errs : Array String := #[]
  for t in paper do
    let n := (rows.filter (·.template == t)).size
    if n > 1 then errs := errs.push s!"template `{t}` has {n} `@[tau_rowA]` rows"
  -- coverage
  let mut rowCover : Std.HashMap (Name × Name) Name := {}
  for r in rows do
    for (s, _) in r.bits do
      if let some other := rowCover.get? (r.template, s) then
        errs := errs.push s!"bit `{r.template} × {s}` is stated by two rows ({other}, {r.name})"
      rowCover := rowCover.insert (r.template, s) r.name
      if expectedFloorBits.any fun e => e.template == r.template && e.slot == s then
        errs := errs.push s!"bit `{r.template} × {s}` is a `‡` cell of the table but {r.name} states it as a ROW \
          slot — a floor that became a theorem; move it to the table's theorem side (update \
          `SPRIME_SOURCE_OF_TRUTH.md` §3 and `expectedFloorBits` together) or restate it as a floor bit"
  let mut floorCover : Std.HashMap (Name × Name) Name := {}
  for f in floors do
    if let some other := floorCover.get? (f.template, f.slot) then
      errs := errs.push s!"floor bit `{f.template} × {f.slot}` is stated twice ({other}, {f.name})"
    floorCover := floorCover.insert (f.template, f.slot) f.name
    if let some r := rowCover.get? (f.template, f.slot) then
      errs := errs.push s!"bit `{f.template} × {f.slot}` is both a row slot ({r}) and a floor bit ({f.name})"
  unless errs.isEmpty do
    throwError "TAU CENSUS (S'): {errs.size} error(s):\n  {"\n  ".intercalate errs.toList}"
  -- gaps
  let mut uncovered : Array String := #[]
  let mut missingFloors : Array String := #[]
  for a in paper do
    for t in paper do
      let isFloor := expectedFloorBits.any fun e => e.template == a && e.slot == t
      if isFloor then
        unless floorCover.contains (a, t) do missingFloors := missingFloors.push s!"{a} × {t}"
      else
        unless rowCover.contains (a, t) do uncovered := uncovered.push s!"{a} × {t}"
  let missingRows := paper.filter fun t => !(rows.any (·.template == t))
  let covered := rowCover.size + floorCover.size
  let summary := s!"tau census (S'): {rows.size}/{paper.size} rows, {rowCover.size} row slots, \
    {floors.size}/{expectedFloorBits.size} floor bits — {covered}/{paper.size * paper.size} bits covered"
  if uncovered.isEmpty && missingFloors.isEmpty && missingRows.isEmpty then
    logInfo s!"{summary}; COMPLETE"
  else
    let gaps := s!"{summary}\n  templates without a row: {missingRows.toList}\n  \
      uncovered theorem slots ({uncovered.size}): {uncovered.toList}\n  \
      missing floor bits ({missingFloors.size}): {missingFloors.toList}"
    if strict then
      throwError "TAU CENSUS (S') is INCOMPLETE (strict):\n  {gaps}"
    else
      logInfo s!"{gaps}\n  (Phase 3 in progress: gaps are informational; `#check_tau_rowsA strict` makes them errors)"

/-- **The build-time gate**: validate every `@[tau_rowA]` row and `@[tau_floor_bitA]` floor bit and run the census
over `paperOrder²`. `#check_tau_rowsA strict` turns coverage gaps into errors. -/
elab "#check_tau_rowsA" s:(&" strict")? : command => do
  runCensus s.isSome

end ArithS.Tau

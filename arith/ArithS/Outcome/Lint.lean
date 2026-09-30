import ArithS.Outcome.Spec
import ArithS.Outcome.Floor
import ArithS.Outcome.Attr
import Lean

/-!
# ArithS.Outcome.Lint — the PA-`S'` outcome-theorem linter

The twin of the engine's `PrisonersDilemma/Outcome/Lint.lean`, for the `OutcomeSpecA` cells of
`Outcome/Matrix/<L>.lean` and the `FloorSpecA` floors of `Outcome/Floors.lean`. Three build-time commands, every
failure a `throwError` (never a warning), so that `lake build` (target `ArithSOutcomeCheck`) rejects a bad theorem:

* `#check_outcomeA_theorems "<matrix dir>"` — **the validator**: every `@[outcomeA]` theorem really is an
  `OutcomeSpecA` application with a literal regime and result whose `L`/`R` bots agree with its NAME; **the
  census**: every declaration under the matrix directory named like a cell (`outcome_<L>_vs_<R>`, both
  alphanumeric, no `_floor` suffix) is tagged — the guard against the opt-in polarity (a forgotten tag would
  silently shrink the export).
* `#check_floorA_theorems "<FloorDichotomy.lean>"` — every `@[floorA]` theorem is a `FloorSpecA` application named
  `outcome_<L>_vs_<R>_floor` whose bots agree with its name and whose dichotomy `dich_<L>_vs_<R>` exists; every
  `theorem dich_<L>_vs_<R>` in that file (exact shape; `_core`/`_full`/`_prudenceFound` variants are not cells) has
  a tagged floor.
* `#check_sprime_coverage` — every unordered pair of the 12 paper base bots (diagonals included) is a tagged cell
  or a tagged floor, in either orientation (`Research/Notes/SPRIME_SOURCE_OF_TRUTH.md` §0.4).

The `OutcomeSpecA`/`FloorSpecA` heads are matched SYNTACTICALLY: they are plain `def`s here, but the engine's
`OutcomeSpec` is a reducible `abbrev` and `whnf` unfolds straight past it — the same discipline keeps the two
linters interchangeable. The hinge of a floor is printed by a hand-rolled printer (`hingeText`), not `ppExpr`, so
the exported text is the same in the elaborator (where `open ArithS` activates the `□[k]` notation) and in the
standalone exporter (where nothing is open and `ppExpr` would print fully qualified names).
-/

open Lean Elab Command Meta

namespace ArithS.Outcome

/-- Metadata recovered from one tagged theorem's elaborated type. -/
structure CellInfo where
  name     : Name
  /-- Defining module, e.g. `ArithS.Outcome.Matrix.DupocBot`. -/
  module   : Name
  leftBot  : Name
  rightBot : Name
  regime   : Name
  /-- Always `0` in `S'`: fuel is existential in `OutcomeSpecA` (kept for schema parity with the engine). -/
  pad      : Nat
  /-- `none` for a proven `= none` (no-outcome) theorem. -/
  pair     : Option (Name × Name)
  /-- `L`/`R` is not a bare pass-through (`bot (fun k => PrudentBot (2*k+64))`, a literal budget). -/
  staggered : Bool
  /-- The two bot arguments, pretty-printed the engine's way: `DupocBot k`, `DBot`. -/
  leftText  : String
  rightText : String
  /-- Floors only: the hinge, printed with the binder named `k` (`""` for a cell). -/
  hinge     : String
  /-- Floors only: the dichotomy this floor is the engine-side half of, `dich_<L>_vs_<R>` (`.anonymous` for a cell). -/
  dichotomy : Name
  deriving Repr

/-- The bare name, e.g. `PD.Bots.CupodBot` ↦ `CupodBot`, `ArithS.Just7` ↦ `Just7`. -/
def shortName : Name → Name
  | .str _ s => Name.mkSimple s
  | n        => n

/-- Strip the `∀`-telescope. A `Prop` binder is REJECTED, as in the engine: a condition on the budget is what the
    `.eventual` regime expresses, a condition on anything else is a floor's hinge, and a floor is stated as
    `FloorSpecA` with the hinge inline. -/
private def stripBinders (tag : String) (n : Name) (ty : Expr) : MetaM Expr := do
  let mut body := ty
  while body.isForall do
    let d := body.bindingDomain!
    if (← isProp d) then
      throwError "@[{tag}] {n}: hypothesis `{← ppExpr d}` in the telescope — a cell takes no side conditions; \
        a floor states its hinge inline (`FloorSpecA … (fun k ↦ …) …`)"
    body := body.bindingBody!.instantiate1 (mkFVar ⟨body.bindingName!⟩)
  return body

/-- A program family `P : ℕ → PD.Prog` (the argument of `bot`) or a program `P : PD.Prog` (of `const`): its head
    constant and whether the budget is anything but the shared `k`. -/
private def progFamilyOf (e : Expr) : Option Name × Bool :=
  match e with
  | .lam _ _ b _ =>
    let ok := b.getAppArgs.all fun a => a.isBVar
    (b.getAppFn.constName?, !ok)
  | _ => (e.getAppFn.constName?, !e.getAppArgs.isEmpty)

/-- Head constant of a bot argument of `OutcomeSpecA`/`FloorSpecA`, plus whether it is staggered.

    Accepted shapes: `bot P` (`P` a bare `ℕ → PD.Prog` constant, or `fun k ↦ X k` — pass-throughs; anything else
    is staggered), `const P` (`P` a bare closed `PD.Prog` constant; `const (X 5)` is a hidden budget, staggered),
    a lambda `fun k ↦ progCode (X k)` / `fun _ ↦ progCode X` (the head of `progCode`'s argument), and a bare
    `ℕ → ℕ` constant such as the hand-template twin `Just7` (its own name; not staggered). -/
private def botOf (e : Expr) : Option Name × Bool :=
  match e.getAppFnArgs with
  | (``ArithS.bot, #[P]) => progFamilyOf P
  | (``ArithS.const, #[P]) => (P.getAppFn.constName?, !P.getAppArgs.isEmpty)
  | _ =>
    match e with
    | .lam _ _ b _ =>
      match b.getAppFnArgs with
      | (``ArithS.progCode, #[Q]) => progFamilyOf Q
      | _ => (b.getAppFn.constName?, !(b.getAppArgs.all fun a => a.isBVar))
    | _ => (e.getAppFn.constName?, !e.getAppArgs.isEmpty)

/-- Print a budget expression: binders by name, literals, `+`/`*` with the usual precedence (the engine's
    `natText`, so the `left`/`right` texts of the two exports agree). -/
private partial def natText (binder : Name) (e : Expr) (prec : Nat := 0) : MetaM String := do
  match e with
  | .bvar _ => return binder.toString
  | .fvar id => return id.name.toString
  | _ =>
    if let some n := e.rawNatLit? then return toString n
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, l, _]) => natText binder l prec
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let t := s!"{← natText binder a 1} + {← natText binder b 1}"
      return if prec > 1 then s!"({t})" else t
    | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      let t := s!"{← natText binder a 2} * {← natText binder b 2}"
      return if prec > 2 then s!"({t})" else t
    | _ => return toString (← ppExpr e)

/-- `head a₁ … aₙ` for a program (family) applied to budget expressions. -/
private def progText (binder : Name) (body : Expr) : MetaM String := do
  let head ← match body.getAppFn.constName? with
    | some c => pure (shortName c).toString
    | none => do return toString (← ppExpr body.getAppFn)
  let mut out := head
  for a in body.getAppArgs do
    out := out ++ " " ++ (← natText binder a 3)
  return out

/-- Print a bot argument as a reader would write it: `bot DupocBot` ↦ `DupocBot k`; `const DBot` ↦ `DBot`;
    `bot (fun k ↦ PrudentBot (2*k+64))` ↦ `PrudentBot (2 * k + 64)`; the twin `Just7` ↦ `Just7 k`. -/
private def botArgText (e : Expr) : MetaM String := do
  let family (P : Expr) : MetaM String := do
    match P with
    | .lam n _ b _ => progText n b
    | _ => progText `k (mkApp P (mkBVar 0))
  match e.getAppFnArgs with
  | (``ArithS.bot, #[P]) => family P
  | (``ArithS.const, #[P]) => progText `k P
  | _ =>
    match e with
    | .lam n _ b _ =>
      match b.getAppFnArgs with
      | (``ArithS.progCode, #[Q]) => progText n Q
      | _ => progText n b
    | _ => family e

/-- Read `Option PD.Outcome` as a literal pair, or `none`. -/
private def resultOf (e : Expr) : MetaM (Option (Option (Name × Name))) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Option.none, _) => return some none
  | (``Option.some, #[_, p]) =>
    match (← whnf p).getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) =>
      let a ← whnf a; let b ← whnf b
      match a.constName?, b.constName? with
      | some an, some bn => return some (some (shortName an, shortName bn))
      | _, _ => return none
    | _ => return none
  | _ => return none

/-- The hinge printer: `□[k] (φ)` for `LenBox TAct k φ`, `∨`/`∧`/`¬` with the usual precedences, otherwise the
    head's short name applied to its EXPLICIT arguments (`guardCodeB (templateCode phiDu) (progCode (DupocBot k))
    (progCode DBot) k`). Deterministic and independent of open namespaces and pretty-printer options. -/
partial def hingeText (e : Expr) (prec : Nat := 0) : MetaM String := do
  let paren (p : Nat) (s : String) : String := if prec > p then s!"({s})" else s
  match e with
  | .fvar id => return id.name.toString
  | .bvar _ => return "k"
  | .const n _ => return (shortName n).toString
  | .mdata _ b => hingeText b prec
  | .lit (.natVal n) => return toString n
  | _ =>
    if let some n := e.rawNatLit? then return toString n
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, l, _]) => hingeText l prec
    | (``Or, #[a, b]) => return paren 30 s!"{← hingeText a 31} ∨ {← hingeText b 30}"
    | (``And, #[a, b]) => return paren 35 s!"{← hingeText a 36} ∧ {← hingeText b 35}"
    | (``Not, #[a]) => return paren 40 s!"¬ {← hingeText a 40}"
    | (``ArithS.LenBox, args) =>
      -- `LenBox {V} [..] {L} [..] (T) [T.Δ₁] (k φ)`: keep the EXPLICIT arguments, `T k φ`.
      let ex ← explicitArgs e.getAppFn args
      let n := ex.size
      if n == 3 && (ex.getD 0 default).isConstOf ``ArithS.TAct then
        return paren 1000 s!"□[{← hingeText (ex.getD 1 default) 0}] ({← hingeText (ex.getD 2 default) 0})"
      else genericApp e
    | _ =>
      if e.getAppArgs.isEmpty then return toString (← ppExpr e)
      genericApp e
where
  /-- The explicit arguments of `f args`, by the binder infos of `f`'s type. -/
  explicitArgs (f : Expr) (args : Array Expr) : MetaM (Array Expr) := do
    let info ← try getFunInfoNArgs f args.size catch _ => pure { paramInfo := #[] }
    let mut out := #[]
    for i in List.range args.size do
      let explicit := if h : i < info.paramInfo.size then info.paramInfo[i].isExplicit else true
      if explicit then out := out.push (args.getD i default)
    return out
  genericApp (e : Expr) : MetaM String := do
    let f := e.getAppFn
    let head ← match f.constName? with
      | some c => pure (shortName c).toString
      | none => do return toString (← ppExpr f)
    let ex ← explicitArgs f e.getAppArgs
    let mut out := head
    for a in ex do
      out := out ++ " " ++ (← hingeText a 1024)
    return if !ex.isEmpty && prec > 1000 then s!"({out})" else out

/-- Split `<prefix>_<L>_vs_<R><suffix>` into its two bot names, or throw. -/
private def namePair (tag : String) (n : Name) (pre suffix : String) : MetaM (String × String) := do
  let base := (shortName n).toString
  unless base.startsWith pre do
    throwError "@[{tag}] {n}: name must be `{pre}<Left>_vs_<Right>{suffix}`"
  unless base.endsWith suffix do
    throwError "@[{tag}] {n}: name must end with `{suffix}`"
  let core := (base.drop pre.length).toString.dropRight suffix.length
  match core.splitOn "_vs_" with
  | [l, r] => return (l, r)
  | _ => throwError "@[{tag}] {n}: name must contain exactly one `_vs_`"

private def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames.getD idx.toNat .anonymous
  | none     => Name.anonymous

/-- Validate one `@[outcomeA]` declaration, returning its exported metadata. -/
def inspectCellA (env : Environment) (n : Name) : MetaM CellInfo := do
  let some ci := env.find? n
    | throwError "@[outcomeA] {n}: not found in the environment"
  let body ← stripBinders "outcomeA" n ci.type
  -- Match the head SYNTACTICALLY (see the module docstring).
  let (fn, args) := (body.getAppFn, body.getAppArgs)
  unless fn.isConstOf ``ArithS.OutcomeSpecA do
    throwError "@[outcomeA] {n} is OFF-TEMPLATE: its statement must be `ArithS.OutcomeSpecA …`, got\n  {← ppExpr body}"
  unless args.size == 4 do
    throwError "@[outcomeA] {n}: expects 4 arguments, got {args.size}"
  let some regime := (← whnf (args.getD (0) default)).constName?
    | throwError "@[outcomeA] {n}: the BudgetRegime must be a literal constructor"
  let (lBot, lStag) := botOf (args.getD (1) default)
  let (rBot, rStag) := botOf (args.getD (2) default)
  let some lB := lBot | throwError "@[outcomeA] {n}: cannot read the LEFT bot from `{← ppExpr (args.getD (1) default)}`"
  let some rB := rBot | throwError "@[outcomeA] {n}: cannot read the RIGHT bot from `{← ppExpr (args.getD (2) default)}`"
  let some pair ← resultOf (args.getD (3) default)
    | throwError "@[outcomeA] {n}: the result must be a literal `none` or `some (.C/.D, .C/.D)`"
  let (nameL, nameR) ← namePair "outcomeA" n "outcome_" ""
  unless (shortName lB).toString == nameL do
    throwError "@[outcomeA] {n}: NAME/STATEMENT MISMATCH — name says left bot `{nameL}`, statement uses `{shortName lB}`"
  unless (shortName rB).toString == nameR do
    throwError "@[outcomeA] {n}: NAME/STATEMENT MISMATCH — name says right bot `{nameR}`, statement uses `{shortName rB}`"
  return { name := n, module := moduleOf env n, leftBot := shortName lB, rightBot := shortName rB
           regime := shortName regime, pad := 0, pair := pair
           staggered := lStag || rStag
           leftText := (← botArgText (args.getD (1) default)), rightText := (← botArgText (args.getD (2) default))
           hinge := "", dichotomy := .anonymous }

/-- Validate one `@[floorA]` declaration: a `FloorSpecA L R hinge r` named `outcome_<L>_vs_<R>_floor`, the hinge
    an inline lambda, the dichotomy `dich_<L>_vs_<R>` present in the environment. Regime `eventual`. -/
def inspectFloorA (env : Environment) (n : Name) : MetaM CellInfo := do
  let some ci := env.find? n
    | throwError "@[floorA] {n}: not found in the environment"
  let body ← stripBinders "floorA" n ci.type
  let (fn, args) := (body.getAppFn, body.getAppArgs)
  unless fn.isConstOf ``ArithS.FloorSpecA do
    throwError "@[floorA] {n} is OFF-TEMPLATE: its statement must be `ArithS.FloorSpecA …`, got\n  {← ppExpr body}"
  unless args.size == 4 do
    throwError "@[floorA] {n}: expects 4 arguments, got {args.size}"
  let (lBot, lStag) := botOf (args.getD (0) default)
  let (rBot, rStag) := botOf (args.getD (1) default)
  let some lB := lBot | throwError "@[floorA] {n}: cannot read the LEFT bot from `{← ppExpr (args.getD (0) default)}`"
  let some rB := rBot | throwError "@[floorA] {n}: cannot read the RIGHT bot from `{← ppExpr (args.getD (1) default)}`"
  let hinge ← match (args.getD (2) default) with
    | .lam _ _ b _ => hingeText (b.instantiate1 (mkFVar ⟨`k⟩))
    | h => throwError "@[floorA] {n}: the hinge must be an inline lambda `fun k ↦ …`, got `{← ppExpr h}`"
  let some pair ← resultOf (args.getD (3) default)
    | throwError "@[floorA] {n}: the result must be a literal `none` or `some (.C/.D, .C/.D)`"
  if pair.isNone then
    throwError "@[floorA] {n}: a floor's engine-side value is a pair, never `none`"
  let (nameL, nameR) ← namePair "floorA" n "outcome_" "_floor"
  unless (shortName lB).toString == nameL do
    throwError "@[floorA] {n}: NAME/STATEMENT MISMATCH — name says left bot `{nameL}`, statement uses `{shortName lB}`"
  unless (shortName rB).toString == nameR do
    throwError "@[floorA] {n}: NAME/STATEMENT MISMATCH — name says right bot `{nameR}`, statement uses `{shortName rB}`"
  let dich := Name.mkSimple s!"dich_{nameL}_vs_{nameR}"
  unless env.contains (`ArithS ++ dich) do
    throwError "@[floorA] {n}: no dichotomy `ArithS.{dich}` in the environment — a floor is the engine-side half \
      of a `dich_<L>_vs_<R>` of `Cells/FloorDichotomy.lean`"
  return { name := n, module := moduleOf env n, leftBot := shortName lB, rightBot := shortName rB
           regime := `eventual, pad := 0, pair := pair
           staggered := lStag || rStag
           leftText := (← botArgText (args.getD (0) default)), rightText := (← botArgText (args.getD (1) default))
           hinge := hinge, dichotomy := dich }

/-- `outcome_<L>_vs_<R>` with both parts alphanumeric and non-empty: the cell shape (a `_floor`/`_staggered`
    suffix makes the right part non-alphanumeric, so variants are simply not cells). -/
def cellShaped (nm : String) : Bool :=
  nm.startsWith "outcome_" &&
    match (nm.drop "outcome_".length).toString.splitOn "_vs_" with
    | [l, r] => !l.isEmpty && !r.isEmpty && l.all Char.isAlphanum && r.all Char.isAlphanum
    | _ => false

/-- Every `theorem <name>` in the text, by name. Text-level on purpose: an UNTAGGED declaration is invisible to
    the environment's attribute state, and finding those is the whole point. -/
def theoremNamesIn (txt : String) : Array String := Id.run do
  let mut found := #[]
  for chunk in (txt.splitOn "theorem ").drop 1 do
    let nm := (chunk.takeWhile fun c => c.isAlphanum || c == '_').toString
    unless nm.isEmpty do found := found.push nm
  return found

/-- Every cell-shaped declaration name in the `.lean` files under `dir`. -/
def cellNamesOnDisk (dir : System.FilePath) : IO (Array String) := do
  let mut found : Array String := #[]
  for entry in (← dir.walkDir) do
    if entry.extension == some "lean" then
      for nm in theoremNamesIn (← IO.FS.readFile entry) do
        if cellShaped nm then found := found.push nm
  return found

/-- Every `dich_<L>_vs_<R>` (exact shape) in the file. -/
def dichNamesOnDisk (file : System.FilePath) : IO (Array String) := do
  let txt ← IO.FS.readFile file
  return (theoremNamesIn txt).filter fun nm =>
    nm.startsWith "dich_" && cellShaped ("outcome_" ++ (nm.drop "dich_".length).toString)

/-- The 12 paper base bots (`SPRIME_SOURCE_OF_TRUTH.md` §0.2). -/
def paperBots : Array String :=
  #["CIMCIC", "CooperateBot", "CupodBot", "CupodTrollBot", "DBot", "DIMCID", "DefectBot", "DupocBot", "EBot",
    "OBot", "PrudentBot", "TitForTatBot"]

/-- The hand-template twins (`ArithS/README.md` §4) read as their base bot for COVERAGE only: the ledger's cell
    for `CupodTrollBot × CupodBot` is `outcome_CupodTroll7_vs_CupodBot`, stated on the seven-variable twin
    because the engine's `CupodTrollBot k` freezes a budget-carrying snapshot no fixed template describes. The
    export keeps the twin's name (`left_bot = "CupodTroll7"`), so a name never claims more than its statement. -/
def twinBase : String → String
  | "Just7" => "JustBot" | "Just" => "JustBot" | "Dupoc" => "DupocBot" | "Cupod" => "CupodBot"
  | "CupodTroll7" => "CupodTrollBot" | s => s

end ArithS.Outcome

namespace ArithS.Outcome

open Lean Elab Command

/-- **The build-time gate for the cells.** `#check_outcomeA_theorems "<matrix dir>"`: validate every tagged cell,
    then the census — every cell-shaped declaration under the directory is tagged. -/
elab "#check_outcomeA_theorems " dir:str : command => do
  let env ← getEnv
  let tagged := taggedOutcomesA env
  let cells ← liftTermElabM <| tagged.mapM fun nm => inspectCellA env nm
  let onDisk ← liftM <| cellNamesOnDisk dir.getString
  let taggedShort := tagged.map fun nm => (shortName nm).toString
  let missing := onDisk.filter fun d => !taggedShort.contains d
  unless missing.isEmpty do
    throwError "S' OUTCOME CENSUS: {missing.size} cell-shaped declaration(s) under {dir.getString} are not \
      `@[outcomeA]`-tagged and would be silently missing from the export:\n  {missing.toList}\nTag them (and state \
      them on the `OutcomeSpecA` template), or rename them if they are not cells."
  -- A pair is stated once per orientation: two tagged cells for the same ordered pair would be rival rows.
  let mut seen : Std.HashSet (Name × Name) := {}
  for c in cells do
    if seen.contains (c.leftBot, c.rightBot) then
      throwError "S' OUTCOME CENSUS: two `@[outcomeA]` cells for {c.leftBot} vs {c.rightBot} (second: {c.name})"
    seen := seen.insert (c.leftBot, c.rightBot)
  logInfo s!"S' outcome census OK — {tagged.size} tagged cells, {onDisk.size} cell-shaped declarations under \
    {dir.getString}"

/-- **The build-time gate for the floors.** `#check_floorA_theorems "<FloorDichotomy.lean>"`: validate every tagged
    floor, then the census — every `dich_<L>_vs_<R>` in the file has a tagged `outcome_<L>_vs_<R>_floor`. -/
elab "#check_floorA_theorems " file:str : command => do
  let env ← getEnv
  let tagged := taggedFloorsA env
  let floors ← liftTermElabM <| tagged.mapM fun nm => inspectFloorA env nm
  let dichs ← liftM <| dichNamesOnDisk file.getString
  let taggedShort := tagged.map fun nm => (shortName nm).toString
  let missing := dichs.filter fun d =>
    !taggedShort.contains s!"outcome_{(d.drop "dich_".length).toString}_floor"
  unless missing.isEmpty do
    throwError "S' FLOOR CENSUS: {missing.size} dichotomy(ies) in {file.getString} have no `@[floorA]` \
      `outcome_<L>_vs_<R>_floor` theorem (`Outcome/Floors.lean`):\n  {missing.toList}"
  -- A floor never shadows a cell of the same ordered pair.
  let cells ← liftTermElabM <| (taggedOutcomesA env).mapM fun nm => inspectCellA env nm
  for f in floors do
    if cells.any fun c => c.leftBot == f.leftBot && c.rightBot == f.rightBot then
      throwError "S' FLOOR CENSUS: {f.name} is a floor for {f.leftBot} vs {f.rightBot}, which also has an \
        `@[outcomeA]` cell — a floor is for a pair `S'` does NOT decide"
  logInfo s!"S' floor census OK — {tagged.size} tagged floors, {dichs.size} dichotomies in {file.getString}"

/-- **Coverage of the paper zoos.** `#check_sprime_coverage`: every unordered pair of the 12 paper base bots
    (diagonals included) is an `@[outcomeA]` cell or an `@[floorA]` floor in either orientation; the
    hand-template twins count for their base bot (`twinBase`). -/
elab "#check_sprime_coverage" : command => do
  let env ← getEnv
  let cells ← liftTermElabM <| (taggedOutcomesA env).mapM fun nm => inspectCellA env nm
  let floors ← liftTermElabM <| (taggedFloorsA env).mapM fun nm => inspectFloorA env nm
  let key (a b : String) : String × String := if a ≤ b then (a, b) else (b, a)
  let mut covered : Std.HashSet (String × String) := {}
  let mut viaTwin : Array String := #[]
  for c in cells ++ floors do
    let l := c.leftBot.toString; let r := c.rightBot.toString
    let (l', r') := (twinBase l, twinBase r)
    if (l' != l || r' != r) && paperBots.contains l' && paperBots.contains r' then
      viaTwin := viaTwin.push s!"{l'} × {r'} (via {c.name})"
    covered := covered.insert (key l' r')
  let mut missing : Array String := #[]
  let mut total := 0
  for i in List.range paperBots.size do
    for j in List.range paperBots.size do
      if i ≤ j then
        total := total + 1
        let (a, b) := (paperBots.getD i "", paperBots.getD j "")
        unless covered.contains (key a b) do
          missing := missing.push s!"{a} × {b}"
  unless missing.isEmpty do
    throwError "S' COVERAGE: {missing.size} of the {total} unordered pairs of the 12 paper base bots have neither \
      an `@[outcomeA]` cell nor an `@[floorA]` floor:\n  {missing.toList}"
  logInfo s!"S' coverage OK — {cells.size} cells, {floors.size} floors, {total}/{total} paper-zoo pairs covered\
    {if viaTwin.isEmpty then "" else s!" ({viaTwin.size} through a hand-template twin: {viaTwin.toList})"}"

end ArithS.Outcome

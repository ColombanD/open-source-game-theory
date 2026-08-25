import PrisonersDilemma.Outcome.Spec
import PrisonersDilemma.Outcome.Attr
import Lean

/-!
# The outcome-theorem linter

Two independent checks, both of which FAIL THE BUILD (`throwError`, never a warning) so
that CI (`lake build`) and the app's `library_writer` transaction both reject bad
theorems for free:

* **the validator** — every `@[outcome]`-tagged theorem really is an `OutcomeSpec`
  application with literal regime/pad/result, and its `L`/`R` bots agree with its NAME
  (nothing previously stopped `outcome_A_vs_B` from being a statement about `C`);
* **the census** — every `outcome_X_vs_Y` declaration on disk is either tagged or listed
  in `Outcome/exclusions.txt`, and the tagged count is exactly the expected number.

The census is the guard against the opt-in polarity inversion: forgetting a tag would
otherwise silently shrink the matrix. Its regex deliberately OVER-approximates — an
over-approximation produces a loud build failure, never a silent omission. Do not
"simplify" it into agreement with the validator.
-/

open Lean Elab Command Meta

namespace PD.Outcome

/-- Metadata recovered from one tagged theorem's elaborated type. -/
structure CellInfo where
  name     : Name
  /-- Defining module, e.g. `PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot`. -/
  module   : Name
  leftBot  : Name
  rightBot : Name
  regime   : Name
  pad      : Nat
  /-- `none` for a proven `= none` (no-outcome) theorem. -/
  pair     : Option (Name × Name)
  /-- Pretty-printed `Prop` binders — the honest replacement for the `h`-prefix guess. -/
  sideConds : Array String
  /-- `L`/`R` is not a bare pass-through, e.g. `fun k => PrudentBot (2*k+64)`. -/
  staggered : Bool
  deriving Repr

/-- Strip the `∀`-telescope, collecting `Prop` binders as side conditions. -/
private def stripBinders (ty : Expr) : MetaM (Expr × Array String) := do
  let mut body := ty
  let mut conds := #[]
  while body.isForall do
    let d := body.bindingDomain!
    if (← isProp d) then
      conds := conds.push (toString (← ppExpr d))
    body := body.bindingBody!.instantiate1 (mkFVar ⟨`_dummy⟩)
  return (body, conds)

/-- Head constant of a bot argument, plus whether it is staggered.

    `CupodBot` / `fun k => CupodBot k` are pass-throughs; `fun _ => OBot` is a closed bot;
    anything else (`fun k => PrudentBot (2*k+64)`, `fun k => LegibleBot (2*k+64) k`) is
    staggered. -/
private def botOf (e : Expr) : MetaM (Option Name × Bool) := do
  match e with
  | .lam _ _ b _ =>
    let f := b.getAppFn
    let args := b.getAppArgs
    -- `fun _ => Bot` (closed) or `fun k => Bot k` (pass-through) are unstaggered.
    let passthrough := args.all fun a => a.isBVar || !a.hasLooseBVars
    let plain := args.all fun a => !a.hasLooseBVars
    return (f.constName?, !(plain || passthrough))
  | _ => return (e.getAppFn.constName?, false)

/-- The bot's bare name, e.g. `PD.Bots.CupodBot` ↦ `CupodBot`. -/
def shortName : Name → Name
  | .str _ s => Name.mkSimple s
  | n        => n

private def natLit? (e : Expr) : MetaM (Option Nat) := do
  match (← whnf e).rawNatLit? with
  | some n => return some n
  | none   => return (← whnf e).nat?

/-- Read `Option Outcome` as a literal pair, or `none`. -/
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

/-- Validate one tagged declaration, returning its exported metadata. -/
def inspectCell (env : Environment) (n : Name) : MetaM CellInfo := do
  let some ci := env.find? n
    | throwError "@[outcome] {n}: not found in the environment"
  let (body, sideConds) ← stripBinders ci.type
  -- Match the head SYNTACTICALLY. `OutcomeSpec` is a reducible `abbrev`, so `whnf`
  -- would happily unfold straight past it to the underlying `outcome … = some …`
  -- equation and then report every on-template theorem as off-template.
  let (fn, args) := (body.getAppFn, body.getAppArgs)
  unless fn.isConstOf ``PD.OutcomeSpec do
    throwError "@[outcome] {n} is OFF-TEMPLATE: its statement must be `PD.OutcomeSpec …`, got\n  {← ppExpr body}"
  unless args.size == 5 do
    throwError "@[outcome] {n}: OutcomeSpec expects 5 arguments, got {args.size}"
  let some regime := (← whnf args[0]!).constName?
    | throwError "@[outcome] {n}: the BudgetRegime must be a literal constructor"
  let some pad ← natLit? args[1]!
    | throwError "@[outcome] {n}: `pad` must be a Nat literal"
  let (lBot, lStag) ← botOf args[2]!
  let (rBot, rStag) ← botOf args[3]!
  let some lB := lBot | throwError "@[outcome] {n}: cannot read the LEFT bot"
  let some rB := rBot | throwError "@[outcome] {n}: cannot read the RIGHT bot"
  let some pair ← resultOf args[4]!
    | throwError "@[outcome] {n}: the result must be a literal `none` or `some (.C/.D, .C/.D)`"
  -- Name/statement agreement: `(llm_)?outcome_<L>_vs_<R>`.
  let base := (shortName n).toString
  let base := if base.startsWith "llm_" then (base.drop 4).toString else base
  unless base.startsWith "outcome_" do
    throwError "@[outcome] {n}: name must be `(llm_)outcome_<Left>_vs_<Right>`"
  let core := (base.drop "outcome_".length).toString
  let parts := core.splitOn "_vs_"
  unless parts.length == 2 do
    throwError "@[outcome] {n}: name must contain exactly one `_vs_`"
  let nameL := parts[0]!; let nameR := parts[1]!
  unless (shortName lB).toString == nameL do
    throwError "@[outcome] {n}: NAME/STATEMENT MISMATCH — name says left bot `{nameL}`, statement uses `{shortName lB}`"
  unless (shortName rB).toString == nameR do
    throwError "@[outcome] {n}: NAME/STATEMENT MISMATCH — name says right bot `{nameR}`, statement uses `{shortName rB}`"
  let module := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none     => Name.anonymous
  return { name := n, module := module, leftBot := shortName lB, rightBot := shortName rB
           regime := shortName regime, pad := pad, pair := pair
           sideConds := sideConds, staggered := lStag || rStag }

/-- Every `outcome_*_vs_*` declaration NAME appearing in the sources under `dir`.

    Deliberately crude and over-approximating (see the module docstring). -/
def declNamesOnDisk (dir : System.FilePath) : IO (Array String) := do
  let mut found : Array String := #[]
  for entry in (← dir.walkDir) do
    if entry.extension == some "lean" then
      let txt ← IO.FS.readFile entry
      for chunk in txt.splitOn "theorem " do
        let nm := (chunk.takeWhile fun c => c.isAlphanum || c == '_').toString
        let core := if nm.startsWith "llm_" then (nm.drop 4).toString else nm
        if core.startsWith "outcome_" && (core.splitOn "_vs_").length == 2 then
          found := found.push nm
  return found

/-- Read the exclusion allowlist: one declaration name per line, `--` comments and blanks
    ignored. -/
def readExclusions (path : System.FilePath) : IO (Array String) := do
  if !(← path.pathExists) then return #[]
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    let line := (line.splitOn "--")[0]!.trimAscii.toString
    -- `--` is the inline-reason marker; `#` starts a banner line.
    if !line.isEmpty && !line.startsWith "#" then out := out.push line
  return out

end PD.Outcome

namespace PD.Outcome

open Lean Elab Command

/-- **The build-time gate.**

    `#check_outcome_theorems "<theorems dir>" "<exclusions file>" expecting <n>`

    Validates every tagged theorem, then runs the census. Errors (not warnings) so that a
    plain `lake build` — and therefore CI and the app's library writer — reject any
    off-template, mis-named, or untagged outcome theorem. -/
elab "#check_outcome_theorems " dir:str " excluding " exc:str
    " expecting " n:num " pending " p:num : command => do
  let expected := n.getNat
  let pendingExpected := p.getNat
  let env ← getEnv
  let tagged := taggedOutcomes env
  -- 1. the validator (throws on the first bad cell)
  liftTermElabM do
    for nm in tagged do
      discard <| inspectCell env nm
  -- 2. the census
  let onDisk ← liftM <| declNamesOnDisk dir.getString
  let excluded ← liftM <| readExclusions exc.getString
  let taggedShort := tagged.map fun nm => (shortName nm).toString
  let known := (taggedShort ++ excluded).toList
  -- MIGRATION MODE. Untagged declarations are tolerated only while the count matches
  -- `pending` exactly, so the number can go DOWN (a directory gets migrated, and the
  -- literal is lowered in the same commit) but never silently UP: a newly added
  -- untagged theorem, or a forgotten tag, still turns the build red. `pending 0` is the
  -- end state, at which point this is the strict census the design calls for.
  let missing := onDisk.filter fun d => !known.contains d
  unless missing.size == pendingExpected do
    if missing.size > pendingExpected then
      throwError "OUTCOME CENSUS: {missing.size} un-migrated declaration(s), expected \
        {pendingExpected}. Something NEW is untagged (or a tag was dropped):\n  \
        {missing.toList}\nTag it, exclude it, or raise `pending` deliberately."
    else
      throwError "OUTCOME CENSUS: only {missing.size} un-migrated declaration(s) remain \
        but `pending` still says {pendingExpected} — lower the literal to \
        {missing.size} (0 once the migration is done)."
  let stale := excluded.filter fun e => !onDisk.contains e
  unless stale.isEmpty do
    throwError "OUTCOME CENSUS: {stale.size} stale exclusion(s) — these no longer exist \
      on disk, so the allowlist is rotting:\n  {stale.toList}"
  unless tagged.size == expected do
    throwError "OUTCOME CENSUS: expected {expected} tagged outcome theorems, found \
      {tagged.size}. If this change is intended, update the `expecting` literal."
  logInfo s!"outcome census OK — {tagged.size} tagged, {excluded.size} excluded, \
    {missing.size} pending migration, {onDisk.size} on disk"

end PD.Outcome

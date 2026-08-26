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
* **the census** — every declaration on disk whose name has the EXACT matrix-cell shape
  `(llm_)outcome_<Left>_vs_<Right>` with `<Left>`/`<Right>` both bot directories under the
  theorems root is `@[outcome]`-tagged.

The census is the guard against the opt-in polarity inversion: forgetting a tag would
otherwise silently shrink the matrix (the cell renders as open). It matches the SAME
acceptance rule as the app's matrix (bot names are alphanumeric, rows are the bot
directories), so regime variants like `outcome_WaryBot_vs_DBot_floor` or tier variants
like `outcome_JustBot2_vs_DBot` are simply not cells and need no allowlist. (An earlier
version over-approximated on purpose and carried a 46-line `exclusions.txt`; the
allowlist was pure maintenance, so the census now agrees with the matrix instead.)
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
  /-- `L`/`R` is not a bare pass-through, e.g. `fun k => PrudentBot (2*k+64)`. -/
  staggered : Bool
  /-- The two bot arguments, pretty-printed — how a companion states its stagger. -/
  leftText  : String
  rightText : String
  deriving Repr

/-- Strip the `∀`-telescope. A `Prop` binder is REJECTED: a condition on the budget is
    what the `.eventual` regime expresses, and a condition on anything else is not a
    matrix cell — so the dagger has exactly ONE machine-read cause, a staggered budget.
    (Until 2026-08-27 such binders were collected and exported as `side_conditions`; no
    cell ever had one once the floors were restated as regimes.) -/
private def stripBinders (n : Name) (ty : Expr) : MetaM Expr := do
  let mut body := ty
  while body.isForall do
    let d := body.bindingDomain!
    if (← isProp d) then
      throwError "@[outcome] {n}: hypothesis `{← ppExpr d}` in the telescope — an outcome \
        theorem takes no side conditions; a budget floor is the `.eventual` regime, a \
        second budget is a `(j : Nat)` binder or a staggered lambda"
    body := body.bindingBody!.instantiate1 (mkFVar ⟨`_dummy⟩)
  return body

/-- Head constant of a bot argument, plus whether it is staggered.

    `CupodBot` / `fun k => CupodBot k` are pass-throughs; `fun _ => OBot` is a closed bot;
    anything else (`fun k => PrudentBot (2*k+64)`, `fun k => LegibleBot (2*k+64) k`) is
    staggered.

    A bot argument mentioning a FREE VARIABLE of the theorem (`(j : Nat) : … (fun _ =>
    CupodTrollBot j) DupocBot …`) is staggered too: `j` is a second, independent budget
    that the shared `k` lambda does not see, so the cell is not the same-budget cell.
    Without this, restating such a theorem as `.eventual` in `k` would silently drop
    its dagger. Literal budgets (`fun _ => CupodBot 5`) are also not the same-budget
    cell and count as staggered. -/
private def botOf (e : Expr) : MetaM (Option Name × Bool) := do
  match e with
  | .lam _ _ b _ =>
    let f := b.getAppFn
    let args := b.getAppArgs
    -- `fun _ => Bot` (closed) or `fun k => Bot k` (pass-through) are unstaggered; a
    -- closed NON-variable argument (a literal, a free budget) is a hidden budget.
    let ok := args.all fun a => a.isBVar
    return (f.constName?, !ok)
  | _ =>
    let args := e.getAppArgs
    return (e.getAppFn.constName?, !args.isEmpty)

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

/-- Validate one tagged declaration, returning its exported metadata.

    `suffix` is the name suffix the declaration is allowed (and required) to carry:
    `""` for a cell, `"_staggered"` for a companion (`inspectCompanion`). -/
def inspectCell (env : Environment) (n : Name) (suffix : String := "") : MetaM CellInfo := do
  let some ci := env.find? n
    | throwError "@[outcome] {n}: not found in the environment"
  let body ← stripBinders n ci.type
  -- Match the head SYNTACTICALLY. `OutcomeSpec` is a reducible `abbrev`, so `whnf`
  -- would happily unfold straight past it to the underlying `outcome … = some …`
  -- equation and then report every on-template theorem as off-template.
  let (fn, rawArgs) := (body.getAppFn, body.getAppArgs)
  -- ONE accepted head. (A guarded `OutcomeSpecIf` variant existed until 2026-08-27; its
  -- sole user was a budget floor in disguise, now an ordinary staggered `.eventual` cell.)
  unless fn.isConstOf ``PD.OutcomeSpec do
    throwError "@[outcome] {n} is OFF-TEMPLATE: its statement must be `PD.OutcomeSpec …`, \
      got\n  {← ppExpr body}"
  unless rawArgs.size == 5 do
    throwError "@[outcome] {n}: expects 5 arguments, got {rawArgs.size}"
  let args := rawArgs
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
    throwError "@[outcome] {n}: name must be `(llm_)outcome_<Left>_vs_<Right>{suffix}`"
  unless base.endsWith suffix do
    throwError "@[outcome] {n}: name must end with `{suffix}`"
  let base := base.dropRight suffix.length
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
           staggered := lStag || rStag
           leftText := toString (← ppExpr args[2]!), rightText := toString (← ppExpr args[3]!) }

/-- Validate one `@[outcome_companion]` declaration: on the template, named
    `…_staggered`, and ACTUALLY staggered — a companion that runs both bots at the shared
    `k` is a rival cell, not a companion. -/
def inspectCompanion (env : Environment) (n : Name) : MetaM CellInfo := do
  let c ← inspectCell env n (suffix := "_staggered")
  unless c.staggered do
    throwError "@[outcome_companion] {n}: not staggered — both bots run at the shared \
      budget, so this is a cell, not a companion (drop the `_staggered` suffix and tag it \
      `@[outcome]`, or stagger it)"
  return c

/-- The bot set: the per-bot theorem directories under `dir` (the app's `library_bots`). -/
def botDirsOnDisk (dir : System.FilePath) : IO (Array String) := do
  let mut out := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) && entry.fileName != "LlmGenerations" then
      out := out.push entry.fileName
  return out

/-- Every declaration NAME under `dir` with the exact matrix-cell shape
    `(llm_)outcome_<Left>_vs_<Right><suffix>`, both bots alphanumeric members of `bots`.
    `suffix = ""` finds cells, `"_staggered"` finds companions. Text-level on purpose:
    an UNTAGGED declaration is invisible to the environment's attribute state, and
    finding those is the whole point. -/
def declNamesOnDisk (dir : System.FilePath) (bots : Array String) (suffix : String := "") :
    IO (Array String) := do
  let mut found : Array String := #[]
  for entry in (← dir.walkDir) do
    if entry.extension == some "lean" then
      let txt ← IO.FS.readFile entry
      for chunk in txt.splitOn "theorem " do
        let nm := (chunk.takeWhile fun c => c.isAlphanum || c == '_').toString
        let core := if nm.startsWith "llm_" then (nm.drop 4).toString else nm
        if core.startsWith "outcome_" && core.endsWith suffix then
          let core := core.dropRight suffix.length
          match (core.drop "outcome_".length).toString.splitOn "_vs_" with
          | [l, r] =>
            if l.all Char.isAlphanum && r.all Char.isAlphanum
                && bots.contains l && bots.contains r then
              found := found.push nm
          | _ => pure ()
  return found

end PD.Outcome

namespace PD.Outcome

open Lean Elab Command

/-- **The build-time gate.**

    `#check_outcome_theorems "<theorems dir>"`

    Validates every tagged theorem, then runs the census. Errors (not warnings) so that a
    plain `lake build` — and therefore CI and the app's library writer — reject any
    off-template, mis-named, or untagged outcome theorem. -/
elab "#check_outcome_theorems " dir:str : command => do
  let env ← getEnv
  let tagged := taggedOutcomes env
  -- 1. the validator (throws on the first bad cell)
  liftTermElabM do
    for nm in tagged do
      discard <| inspectCell env nm
  -- 2. the census: every cell-shaped declaration on disk is tagged.
  let bots ← liftM <| botDirsOnDisk dir.getString
  let onDisk ← liftM <| declNamesOnDisk dir.getString bots
  let taggedShort := tagged.map fun nm => (shortName nm).toString
  let missing := onDisk.filter fun d => !taggedShort.contains d
  unless missing.isEmpty do
    throwError "OUTCOME CENSUS: {missing.size} matrix-cell declaration(s) are not \
      `@[outcome]`-tagged and would be silently missing from the matrix:\n  \
      {missing.toList}\nTag them (and state them on the `OutcomeSpec` template), or \
      rename them if they are not cells (a regime variant takes a suffix, e.g. `_floor`)."
  -- 3. the companions: validated, every `…_staggered` declaration on disk is tagged
  --    (a staggered result must not quietly become invisible), and every companion has
  --    a cell for its pair (either orientation).
  let companions := taggedCompanions env
  let cinfos ← liftTermElabM <| companions.mapM fun nm => inspectCompanion env nm
  let cells ← liftTermElabM <| tagged.mapM fun nm => inspectCell env nm
  let cOnDisk ← liftM <| declNamesOnDisk dir.getString bots (suffix := "_staggered")
  let cShort := companions.map fun nm => (shortName nm).toString
  let cMissing := cOnDisk.filter fun d => !cShort.contains d
  unless cMissing.isEmpty do
    throwError "OUTCOME CENSUS: {cMissing.size} `…_staggered` declaration(s) are not \
      `@[outcome_companion]`-tagged, so the matrix would not know the pair is \
      budget-sensitive:\n  {cMissing.toList}"
  for c in cinfos do
    let hasCell := cells.any fun x =>
      (x.leftBot == c.leftBot && x.rightBot == c.rightBot)
      || (x.leftBot == c.rightBot && x.rightBot == c.leftBot)
    unless hasCell do
      throwError "OUTCOME CENSUS: companion {c.name} has no `@[outcome]` cell for \
        {c.leftBot} vs {c.rightBot} (either orientation) — a companion annotates a cell"
  logInfo s!"outcome census OK — {tagged.size} tagged, {onDisk.size} cell-shaped \
    declarations on disk, {bots.size} bot directories, {companions.size} staggered \
    companions"

/-- `#validate_outcome <ident>` — run the validator on ONE declaration and report its
    cell metadata. The app's verdict gate appends this to a submitted (not yet landed)
    proof file, so an off-template, mis-named or untagged LLM theorem is rejected by the
    SAME code that guards the library build — before a human ever sees it. -/
elab "#validate_outcome " id:ident : command => do
  let n ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  unless outcomeAttr.hasTag env n do
    throwError "#validate_outcome {n}: not tagged `@[outcome]` — put the attribute on the \
      line directly above `theorem` (and `import PrisonersDilemma.Outcome`)"
  let c ← liftTermElabM <| inspectCell env n
  let pair := match c.pair with
    | none => "none"
    | some (a, b) => s!"({a}, {b})"
  logInfo s!"outcome cell OK — {c.leftBot} vs {c.rightBot}: {pair}, regime {c.regime}, \
    pad {c.pad}, staggered {c.staggered}"

end PD.Outcome

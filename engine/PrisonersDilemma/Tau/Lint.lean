import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr
import PrisonersDilemma.Outcome.Lint
import Lean

/-!
# The tau row linter

`Outcome/Lint.lean` for `RowSpec`: every `@[tau_row]` theorem is an unconditional
`RowSpec <template> <order> <row>` whose template is a literal `Tmpl` constructor, whose
order is `tauOrder`/`tauOrderInit`, and whose row EVALUATES (by `whnf`) to a literal
action at every slot — the bits the app reads come from the kernel-checked type, not
from a regex over the source. The census is by ROSTER: every constructor of `Tmpl` has
exactly one tagged row, so adding a template without its row fails the build.
-/

open Lean Elab Command Meta

namespace PD.Tau

structure RowInfo where
  name     : Name
  module   : Name
  template : Name
  /-- `tauOrder` or `tauOrderInit`. -/
  order    : Name
  /-- `(slot, action)` in order, actions `C`/`D`. -/
  bits     : Array (Name × Name)
  deriving Repr

/-- `whnf` a closed `List Tmpl` term down to its constructor names. -/
partial def listCtors (e : Expr) : MetaM (Array Name) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return #[]
  | (``List.cons, #[_, h, t]) =>
    let some c := (← whnf h).constName?
      | throwError "tau row: order entry is not a constructor: {← ppExpr h}"
    return #[c] ++ (← listCtors t)
  | _ => throwError "tau row: order is not a list literal: {← ppExpr e}"

/-- Validate one tagged row, returning its bits. -/
def inspectRow (env : Environment) (n : Name) : MetaM RowInfo := do
  let some ci := env.find? n
    | throwError "@[tau_row] {n}: not found in the environment"
  let ty := ci.type
  if ty.isForall then
    throwError "@[tau_row] {n}: a row takes no hypotheses — `RowSpec` quantifies the \
      budget itself (`∃ k₂, ∀ k > k₂, …`); discharge floors and Löb gates inside"
  let (fn, args) := (ty.getAppFn, ty.getAppArgs)
  unless fn.isConstOf ``PD.Tau.RowSpec do
    throwError "@[tau_row] {n} is OFF-TEMPLATE: its statement must be \
      `PD.Tau.RowSpec <template> <order> <row>`, got\n  {← ppExpr ty}"
  unless args.size == 3 do
    throwError "@[tau_row] {n}: expects 3 arguments, got {args.size}"
  let some tmpl := (← whnf args[0]!).constName?
    | throwError "@[tau_row] {n}: the template must be a literal `Tmpl` constructor"
  let some orderName := args[1]!.constName?
    | throwError "@[tau_row] {n}: the order must be `tauOrder` or `tauOrderInit`"
  unless orderName == ``PD.Tau.tauOrder || orderName == ``PD.Tau.tauOrderInit do
    throwError "@[tau_row] {n}: the order must be `tauOrder` or `tauOrderInit`, got {orderName}"
  let slots ← listCtors args[1]!
  let mut bits : Array (Name × Name) := #[]
  for s in slots do
    let v ← whnf (mkApp args[2]! (mkConst s))
    match v.constName? with
    | some c =>
      unless c == ``PD.Action.C || c == ``PD.Action.D do
        throwError "@[tau_row] {n}: row at {s} is not a literal action: {← ppExpr v}"
      bits := bits.push (PD.Outcome.shortName s, PD.Outcome.shortName c)
    | none => throwError "@[tau_row] {n}: row at {s} does not evaluate to an action: {← ppExpr v}"
  let expected := (PD.Outcome.shortName tmpl).toString ++ "RowSpec"
  unless (PD.Outcome.shortName n).toString == expected do
    throwError "@[tau_row] {n}: NAME/STATEMENT MISMATCH — the statement is about \
      `{PD.Outcome.shortName tmpl}`, so the theorem must be named `{expected}`"
  let module := match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none     => Name.anonymous
  return { name := n, module := module, template := PD.Outcome.shortName tmpl
           order := PD.Outcome.shortName orderName, bits := bits }

/-- Validate every tagged row (throws on the first bad one). -/
def inspectAllRows (env : Environment) : MetaM (Array RowInfo) := do
  let mut acc := #[]
  for n in PD.Outcome.taggedTauRows env do
    acc := acc.push (← inspectRow env n)
  return acc

/-- **The build-time gate**: validate every `@[tau_row]` theorem and run the roster
    census — every constructor of `Tmpl` has exactly one row. -/
elab "#check_tau_rows" : command => do
  let env ← getEnv
  let rows ← liftTermElabM <| inspectAllRows env
  let some (.inductInfo ind) := env.find? ``PD.Tau.Tmpl
    | throwError "#check_tau_rows: `PD.Tau.Tmpl` not found"
  let mut missing : Array Name := #[]
  let mut dups : Array Name := #[]
  for c in ind.ctors do
    let short := PD.Outcome.shortName c
    let n := (rows.filter (·.template == short)).size
    if n == 0 then missing := missing.push short
    if n > 1 then dups := dups.push short
  unless missing.isEmpty && dups.isEmpty do
    throwError "TAU CENSUS: templates without a `@[tau_row]` row: {missing.toList}; \
      templates with more than one: {dups.toList}"
  logInfo s!"tau census OK — {rows.size} rows for {ind.ctors.length} templates"

end PD.Tau

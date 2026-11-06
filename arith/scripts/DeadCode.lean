import ArithS
import Lean
/-! `scripts/DeadCode.lean` — the reachability audit of `ArithS` (2026-09-28; restored 2026-10-29 with the
claims-root mode). Not imported by the package.
Run: `cd arith && lake env lean --run scripts/DeadCode.lean <roots.txt> <out.tsv>`; without args it reads
`scripts/roots.txt` and writes `scripts/deadcode.tsv`. ROOTS = the names in `roots.txt` (the `#print axioms`
census; regenerate it with `grep -rhoE "#print axioms [^ ]+" ArithS/Audit/*.lean ArithS/Audit.lean | awk
'{print $3}' | sort -u`) + every instance + every macro/syntax in `ArithS.*` + (claims mode) every non-aux
constant of a module whose name starts with one of the comma-separated prefixes in `DEADCODE_ROOT_MODULES`
(e.g. `ArithS.Outcome.,ArithS.Tau.Rows.`) — with an empty roots file that audits reachability from the
package's CLAIMS alone, independently of what the census prints. LIVE = closure of ROOTS over the constants used
in the TYPE and VALUE of each constant (so `simp` lemmas and auxiliary lemmas used inside proofs are live),
restricted to `ArithS.*`. Output TSV: name, module, kind, startLine, endLine, LIVE|DEAD|ROOT, isAux. -/
open Lean Meta

def isArith (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames.getD i.toNat .anonymous).toString.startsWith "ArithS"
  | none => false

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

def isAuxName (n : Name) : Bool :=
  let s := n.toString
  n.isInternal || hasSub s "._" || hasSub s "match_" || hasSub s "_proof_" || hasSub s "_eq_" ||
  hasSub s "_unsafe_rec" || hasSub s ".proof_" || hasSub s "_sunfold" || hasSub s ".eq_" ||
  hasSub s ".induct" || hasSub s ".brecOn" || hasSub s ".below" || hasSub s ".rec" || hasSub s ".casesOn" ||
  hasSub s ".noConfusion" || hasSub s ".sizeOf" || hasSub s ".injEq" || hasSub s ".mk.inj" || hasSub s ".ibelow" ||
  hasSub s ".binductionOn" || hasSub s "_spec_" || hasSub s ".ofNat" || hasSub s ".toCtorIdx"

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"

def usedOf (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci.value? (allowOpaque := true) with | some v => t ++ v.getUsedConstants | none => t   -- theorems' proofs count (default `value?` hides them)

unsafe def main (args : List String) : IO Unit := do
  let rootsPath := args.getD 0 "scripts/roots.txt"
  let outPath := args.getD 1 "scripts/deadcode.tsv"
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := `ArithS}] {} 0
  let rootLines := (← IO.FS.readFile rootsPath).splitOn "\n" |>.filter (· ≠ "") |>.map String.trim
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if isArith env n then names := names.push n
  let rootSet : Std.HashSet String := Std.HashSet.ofList rootLines
  let prefixes := ((← IO.getEnv "DEADCODE_ROOT_MODULES").getD "").splitOn "," |>.filter (· ≠ "")
  let mut roots : Std.HashSet Name := {}
  for n in names do
    let s := n.toString
    let modName := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames.getD i.toNat .anonymous).toString | none => ""
    if !isAuxName n && prefixes.any (fun p => modName.startsWith p) then roots := roots.insert n
    let bare := if s.startsWith "ArithS." then (s.drop 7).toString else s
    if rootSet.contains s || rootSet.contains bare then roots := roots.insert n
    if (instanceExtension.getState env).instanceNames.contains n then roots := roots.insert n
    if hasSub s "«" then roots := roots.insert n   -- macros / syntax / notation
  let mut live : Std.HashSet Name := roots
  let mut stack : Array Name := roots.toArray
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut deps := usedOf ci
      match ci with
      | .inductInfo ii => deps := deps ++ ii.ctors.toArray ++ ii.all.toArray
      | .ctorInfo c => deps := deps.push c.induct
      | _ => pure ()
      for d in deps do
        if isArith env d && !live.contains d then
          live := live.insert d
          stack := stack.push d
  let mut out := "name\tmodule\tkind\tstart\tend\tstatus\taux\n"
  for n in names do
    let some ci := env.find? n | continue
    let modName := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames.getD i.toNat .anonymous).toString | none => "?"
    let (s, e) := match declRangeExt.find? env n with
      | some r => (r.range.pos.line, r.range.endPos.line)
      | none => (0, 0)
    let status := if roots.contains n then "ROOT" else if live.contains n then "LIVE" else "DEAD"
    out := out ++ s!"{n}\t{modName}\t{kindOf ci}\t{s}\t{e}\t{status}\t{isAuxName n}\n"
  IO.FS.writeFile outPath out
  IO.println s!"ArithS constants {names.size}; roots {roots.size}; live {live.size}; dead {names.size - live.size}"
